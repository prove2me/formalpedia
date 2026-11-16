-- Prove2me | Theorems.Thm_FairTeamContracts_Supplement_theorem_5_2
-- name    : FairTeamContracts.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:10:43.798566+00:00
-- url     : https://prove2.me/theorems/14a54152-c3bf-4447-94e8-758ff3f0aba5
-- title:
--   Theorem 5.2 — an FPTAS for fair team contracts with additive rewards, revenue $\ge(1-\gamma)^2\,\mathrm{OPT}$
-- statement:
--   Suppose that the success function is additive and let $\mathrm{OPT}$ be the revenue of an optimal fair contract. For any $\gamma\in(0,1]$, there is an algorithm that returns a fair contract with revenue at least $(1-\gamma)^2\cdot\mathrm{OPT}$ in time polynomial in the instance size and $1/\gamma$.
--
--   Precisely, there are one Turing machine $M$ and one exponent $k$ such that for every admissible rational additive instance $I$ and every rational $\gamma\in(0,1]$, on input $x=\mathrm{code}(I)\,\mathrm{code}(\gamma)$:
--
--   1. $M$ halts within $(|x|+\lceil1/\gamma\rceil)^k+k$ steps;
--   2. its output is the code of a team $S$ with rational shares $\alpha$ such that $(S,\alpha)$ is a fair contract of $I$ and
--   $$\mathrm{Rev}(S,\alpha)\ge(1-\gamma)^2\cdot\mathrm{OPT}.$$
--
--   Together with Theorem 5.1 this settles the additive case: computing the optimum exactly is NP-hard, but it can be approximated to any relative accuracy in fully polynomial time.
--
--   **Formalization Note** The machine is the published `CookPvsNP.TM`, and the output convention is that of `CookPvsNP.PolyTimeComputable`. The guarantee covers every admissible instance, including $\mathrm{OPT}=0$, agents with $f(i)=0$ and agents with $c_i>f(i)$. $\gamma=1$ is allowed.
--
--   Differences from the source:
--   - reading: "for any γ ∈ (0, 1], there exists an algorithm … in time polynomial in the instance size and 1/γ" → one machine that takes γ as part of its input, with one polynomial bound (|x| + ⌈1/γ⌉)^k + k for every γ; reason: the theorem is titled an FPTAS and the last paragraph of its proof (p.24) calls the result an FPTAS; the uniform reading is the stronger one
--   - reading: instance size → |x|, the total length of the input code(I) code(γ); reason: the machine must read γ to use it, and the instance code is a prefix of x
--   - encoding: additive success function with rational inputs → admissible RatAddInst written in binary, with real success function f(S) = Σ_{i∈S} f(i); the output is a team and rational shares, written as a membership bit and a share for every agent; reason: p.19 "Contributions and costs are rational inputs"; shares off the team are not read
--   - encoding: algorithm and running time (no machine named) → the one-tape Turing machines of the published CookPvsNP_defs, counting steps; reason: the standard machine model of the bit model
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Theorem 5.2, p.20 (PDF 21); proof pp.19–24, Appendices F and H

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_FairTeamContracts_IsFair
import Definitions.Def_FairTeamContracts_rev
import Definitions.Def_FairTeamContracts_optFair
import Definitions.Def_FairTeamContracts_Supplement_RatAddInst

namespace FairTeamContracts.Supplement

/-- **Theorem 5.2 (FPTAS for Additive Reward Functions)** (Chen, Castiglioni, Li, *Fair Team
Contracts*, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Theorem 5.2, p.20; proof pp.20–24,
Appendices F and H): "Suppose that the success function is additive and let OPT be the revenue of
optimal fair contract. For any γ ∈ (0, 1], there exists an algorithm that returns a fair contract
with revenue at least (1 − γ)² · OPT in time polynomial in the instance size and 1/γ."

There is one Turing machine `M` (over a finite tape alphabet containing the code alphabet via
`ι`) and one exponent `k` such that, for every admissible rational additive instance `I` and every
rational `γ ∈ (0, 1]`, on the input `x = code(I) code(γ)`:

1. `M` halts within `(|x| + ⌈1/γ⌉)^k + k` steps, and
2. its output is the code of a team `S` with rational shares `α` such that `(S, α)` is a fair
   contract of `I` with revenue `Rev(S, α) ≥ (1 − γ)² · OPT`.

**Formalization Note.** The machine is the published `CookPvsNP.TM` and the output convention is
that of `CookPvsNP.PolyTimeComputable`. `γ` is part of the input and the polynomial does not
depend on it (an FPTAS, as the theorem's title and the last paragraph of its proof, p.24, say);
`|x|` counts the code of `γ` as well as the code of the instance. Instances are `RatAddInst` with
`Valid`; OPT is the published `optFair`. -/
theorem theorem_5_2 :
    ∃ (Tape : Type) (_ : Fintype Tape) (ι : CSym ↪ Tape) (M : CookPvsNP.TM Tape) (k : ℕ),
      ∀ (I : RatAddInst), I.Valid → ∀ γ : ℚ, 0 < γ → γ ≤ 1 →
        M.HaltsWithin (((encInst I ++ encRat γ).length + ⌈1 / γ⌉₊) ^ k + k)
            ((encInst I ++ encRat γ).map ι) ∧
        ∃ (S : Finset (Fin I.n)) (α : Fin I.n → ℚ),
          M.output (M.run (((encInst I ++ encRat γ).length + ⌈1 / γ⌉₊) ^ k + k)
              (M.init ((encInst I ++ encRat γ).map ι))) = (encContract S α).map (some ∘ ι) ∧
          IsFair I.f I.cost S (fun i => (α i : ℝ)) ∧
          (1 - (γ : ℝ)) ^ 2 * optFair I.f I.cost ≤ rev I.f S (fun i => (α i : ℝ)) := by sorry

end FairTeamContracts.Supplement
