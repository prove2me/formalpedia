-- Prove2me | Theorems.Thm_FairTeamContracts_Supplement_theorem_5_1
-- name    : FairTeamContracts.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:10:02.447705+00:00
-- url     : https://prove2.me/theorems/81ba69bf-f338-4309-b7f8-edcb483822cd
-- title:
--   Theorem 5.1 — computing an optimal fair contract is NP-hard (additive rewards)
-- statement:
--   It is NP-hard to compute an optimal fair contract with additive reward functions.
--
--   For a rational additive instance $I$ (singleton contributions $f(i)\ge0$ with $\sum_i f(i)\le1$, costs $c_i\ge0$), an **optimal fair contract** is a team $S$ with rational shares $\alpha$ such that $(S,\alpha)$ is fair (Definition 2.2) and $\mathrm{Rev}(S,\alpha)=\mathrm{OPT}$. Two statements hold.
--
--   1. **Reduction.** For every language $L$ in NP over a finite nonempty alphabet there are a polynomial-time computable map $g$, sending every string $x$ to the code of an admissible rational additive instance $I_x$, and a polynomial-time decidable language $D$ of pairs, such that for every string $x$ and **every** optimal fair contract $(S,\alpha)$ of $I_x$
--   $$x\in L\iff x\,\#\,\mathrm{code}(S,\alpha)\in D.$$
--   2. **Consequence.** If a polynomial-time computable function maps the code of every admissible rational additive instance to the code of one of its optimal fair contracts, then $\mathrm{NP}\subseteq\mathrm P$ over every finite nonempty alphabet.
--
--   So the minimum-share characterization, which settles the shares for a fixed team, cannot be turned into an efficient exact algorithm: the hardness lies in choosing the team. This motivates the FPTAS of Theorem 5.2.
--
--   **Formalization Note** Turing machines, polynomial time, $\mathrm P$ and $\mathrm{NP}$ are the published `CookPvsNP` definitions. The statement is unconditional ($\mathrm P\ne\mathrm{NP}$ is not assumed), and the solver of clause 2 must handle every admissible instance, not only the instances of the reduction.
--
--   Differences from the source:
--   - reading: "NP-hard to compute an optimal fair contract" (no reduction notion named) → (1) every NP language reduces to the problem with one query, by a polynomial-time instance map and a polynomial-time decidable pair language that is correct for every optimal fair contract returned, and (2) a polynomial-time solver on all admissible instances gives NP ⊆ P; reason: the standard meaning of NP-hardness for a search problem; (1) is what the threshold reduction of Appendix G gives, and (2) is its usual consequence, stated as well so that neither the stronger nor the weaker reading is lost
--   - encoding: additive reward functions with rational inputs → admissible `RatAddInst` (rational f(i) ≥ 0 with Σ f(i) ≤ 1, rational c_i ≥ 0) written in binary over a 4-letter alphabet, with real success function f(S) = Σ_{i∈S} f(i); reason: p.19 "Contributions and costs are rational inputs"; Σ f(i) ≤ 1 is the model's f ≤ 1 for additive f
--   - encoding: an optimal fair contract → IsFair ∧ rev = optFair (the supremum over fair contracts) with rational shares, written as a membership bit and a share for every agent; reason: an optimal fair contract with rational shares exists for every rational instance (the least-incentive contract of Theorem 3.2 on an optimal team), and shares off the team are not read by IsFair or rev
--   - encoding: algorithms and polynomial time (no machine named) → the one-tape Turing machines of the published CookPvsNP_defs; reason: the standard machine model of the bit model
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Theorem 5.1, p.19 (PDF 20); proof Appendix G, pp.55–57 (PDF 56–58)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_FairTeamContracts_IsFair
import Definitions.Def_FairTeamContracts_rev
import Definitions.Def_FairTeamContracts_optFair
import Definitions.Def_FairTeamContracts_Supplement_RatAddInst

namespace FairTeamContracts.Supplement

/-- **Theorem 5.1** (Chen, Castiglioni, Li, *Fair Team Contracts*, arXiv:2512.19388 (manuscript
sha256 b8a12d9b…), Theorem 5.1, p.19; proof Appendix G, pp.55–57): "It is NP-hard to compute an
optimal fair contract with additive reward functions."

An *optimal fair contract* of a rational additive instance `I` is a team `S` with rational shares
`α` such that `(S, α)` is fair for the real additive success function and costs of `I` and its
revenue equals `OPT = optFair`. The statement has two clauses.

1. (*Reduction.*) Every NP language `L` over every finite nonempty alphabet reduces to the
   problem with one query: a polynomial-time map `g` sends each string `x` to the code of an
   admissible rational additive instance, and a polynomial-time decidable language `D` of pairs
   recovers membership from any optimal fair contract of that instance:
   `x ∈ L ↔ x # code(S, α) ∈ D` for **every** optimal fair contract `(S, α)` of the instance.
2. (*Consequence.*) If some polynomial-time computable function maps the code of every admissible
   rational additive instance to the code of an optimal fair contract of it, then `NP ⊆ P` over
   every finite nonempty alphabet.

**Formalization Note.** Machines, polynomial time, `P` and `NP` are the published `CookPvsNP`
ones. Instances are `RatAddInst` with `Valid` (`f(i) ≥ 0`, `∑ f(i) ≤ 1`, `cᵢ ≥ 0`), written in
binary by `encInst`; contracts are written by `encContract` (shares off the team are ignored by
`IsFair` and `rev`). The statement is unconditional (no `P ≠ NP`), and the solver of clause 2 must
work on every admissible instance, not only on the instances of the reduction. -/
theorem theorem_5_1 :
    (∀ (Sym : Type) [Fintype Sym] [Nonempty Sym] (L : CookPvsNP.Lang Sym),
      L ∈ CookPvsNP.NP Sym →
      ∃ g : List Sym → List CSym, CookPvsNP.PolyTimeComputable g ∧
        (∀ x, ∃ I : RatAddInst, I.Valid ∧ g x = encInst I) ∧
        ∃ D : CookPvsNP.Lang (Option (Sym ⊕ CSym)), D ∈ CookPvsNP.P (Option (Sym ⊕ CSym)) ∧
          ∀ (x : List Sym) (I : RatAddInst), I.Valid → g x = encInst I →
            ∀ (S : Finset (Fin I.n)) (α : Fin I.n → ℚ),
              IsFair I.f I.cost S (fun i => (α i : ℝ)) →
              rev I.f S (fun i => (α i : ℝ)) = optFair I.f I.cost →
              (x ∈ L ↔ pairStr x (encContract S α) ∈ D)) ∧
    ((∃ F : List CSym → List CSym, CookPvsNP.PolyTimeComputable F ∧
        ∀ I : RatAddInst, I.Valid → ∃ (S : Finset (Fin I.n)) (α : Fin I.n → ℚ),
          F (encInst I) = encContract S α ∧
          IsFair I.f I.cost S (fun i => (α i : ℝ)) ∧
          rev I.f S (fun i => (α i : ℝ)) = optFair I.f I.cost) →
      ∀ (Sym : Type) [Fintype Sym] [Nonempty Sym], CookPvsNP.NP Sym ⊆ CookPvsNP.P Sym) := by sorry

end FairTeamContracts.Supplement
