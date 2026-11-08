-- Prove2me | Theorems.Thm_AvoidPlast_theorem_4_1
-- name    : AvoidPlast.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:51:12.544577+00:00
-- url     : https://prove2.me/theorems/90941c4c-9f42-4b9f-9a92-d964cd22ea72
-- title:
--   Theorem 4.1 — a PCP for non-deterministic sublinear time
-- statement:
--   There is a universal constant $c_0$ such that the following holds. Let $\varepsilon\in(0,1)$, let $s\ge2^{-\mathrm{polylog}(n)}$ and let $L\in\mathrm{NTIME}[n^\varepsilon]$. There is a probabilistic verifier $V$ that gets input $x\in\{0,1\}^n$ and oracle access to a proof $\pi$ of size $n^{O(\varepsilon)}$ (at most $n^{c_0\varepsilon}$ for large $n$) with the following properties.
--
--   1. **Completeness**: for $x\in L$ there is $\pi$ with $\Pr[V^\pi(x)=1]=1$.
--   2. **Soundness**: for $x\notin L$ and every $\pi'$, $\Pr[V^{\pi'}(x)=0]\ge1-s$.
--   3. **Complexity**: $V$ runs in time $\mathrm{poly}(n)$ and space $\mathrm{polylog}(n)$, and non-adaptively queries $\mathrm{polylog}(n)$ positions in $\pi$.
--
--   Moreover, the accepting proof can be deterministically computed in time $\mathrm{poly}(n)$ from $x$ and the witness. This is the PCP whose low-space verifier drives the main theorem.
--
--   Differences from the source:
--   - generalization: no bound stated on the random bits and the lengths → the verifier uses $\mathrm{polylog}(n)$ random bits and the proof and randomness lengths are nice; reason: Theorem 5.12's proof reads these off Theorem 4.1 ("using $r(n)=\mathrm{polylog}(n)$ random bits", p.28) and the proof of Theorem 4.1 gives them; dropping the clauses gives the printed theorem
--   - encoding: $L\in\mathrm{NTIME}[n^\varepsilon]$, verifier time $O(n^\varepsilon)$ and an $n^\varepsilon$-size witness → verifier time and witness length at most $C(\lceil n^\varepsilon\rceil+1)$; reason: the $O(\cdot)$ of p.18; the bound is an integer that a machine can check
--   - reading: the machine model is the RAM model (p.13), unspecified → a multitape machine with read-only input tapes, each accessed by head moves and index jumps, a fixed work alphabet and a write-only output; reason: the page does not fix a RAM; FP and space $n^\gamma$ are robust under the choice, and sublinear time needs the random access; reading R5
--   - encoding: polylog, poly and $O(\cdot)$ → explicit existential constants $a$, with $\log_2 T(m)+2$ as the base; reason: makes the parameters first-order statements
--   - encoding: proof of size $n^{O(\varepsilon)}$ → exact length $\ell(n)\le n^{c_0\varepsilon}$ for large $n$, with $c_0$ universal and before $\varepsilon$; reason: proofs are padded to exact length as on p.28, and Theorem 5.12 calls the constant universal
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 4.1, p.17

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_ceilPow
import Definitions.Def_AvoidPlast_IsNTimeVerifier
import Definitions.Def_AvoidPlast_PCPSystem
import Definitions.Def_AvoidPlast_IsPCPSystem
import Definitions.Def_AvoidPlast_IsQuasiBounded

namespace AvoidPlast

/-- Theorem 4.1, a PCP for non-deterministic sublinear time (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.17). There is a universal `c₀`
(the `O(·)` of the proof size `n^{O(ε)}`) such that for `ε ∈ (0,1)`, `s ≥ 2^{-polylog(n)}` and
`L ∈ NTIME[n^ε]`, there is a verifier getting `x` and oracle access to a proof of size `≤ n^{c₀ε}`:
perfect completeness, soundness error `s`, time `poly(n)`, space `polylog(n)`, `polylog(n)` non-adaptive
queries, and accepting proofs computable in time `poly(n)` from `x` and the witness.

**Formalization Note** See `IsPCPSystem` for the complexity clauses, including the randomness length,
which Theorem 5.12's proof reads off Theorem 4.1. The bound on the proof size is for large `n`. -/
theorem theorem_4_1 : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∀ (L : Set (List Bool)) (V₀ : Machine 2) (C : ℕ), IsNTimeVerifier V₀ L (ceilPow ε) C →
    ∀ s : ℕ → ℝ, IsQuasiBounded s →
      ∃ S : PCPSystem, IsPCPSystem S L V₀ (ceilPow ε) C s ∧
        ∀ᶠ n : ℕ in Filter.atTop, (S.proofLen n : ℝ) ≤ (n : ℝ) ^ (c₀ * ε) := by sorry

end AvoidPlast
