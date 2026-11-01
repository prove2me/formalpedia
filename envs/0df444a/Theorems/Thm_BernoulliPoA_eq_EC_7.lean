-- Prove2me | Theorems.Thm_BernoulliPoA_eq_EC_7
-- name    : BernoulliPoA.eq_EC_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:44:53.066761+00:00
-- url     : https://prove2.me/theorems/27c1ecf2-4327-4734-a4f5-5f6d5c1a0d1c
-- title:
--   Proof of Theorem 3, Case 2, (EC.7), pp.ec3–ec4 — reduction to a finite family of triples
-- statement:
--   Let $\mathcal C$ be a family of nonnegative nondecreasing costs with $c(k)>0$ for all $c\in\mathcal C\setminus\{c_0\}$ and $k\ge1$, and let $q\in(0,1]$. For each $M\ge 0$ with $M<\gamma_{\mathsf{pr}}(\mathcal C,q)$ there is a finite nonempty set $\mathcal F\subset\mathcal T$ containing a triple $(c,1,0)$ such that
--   $$
--   \Psi_{\mathcal F}(\omega)>M\qquad\text{for all }\omega\ge 0,
--   $$
--   and $\Psi_{\mathcal F}$ attains its minimum over $\omega\ge0$ at some $\bar\omega\ge0$.
--
--   The tight examples are built from this finite family.
--
--   Differences from the source:
--   - encoding: each M < γpr(C,q) → M ∈ ℝ≥0; reason: negative M is covered by M = 0 once T ≠ ∅, and T = ∅ gives γpr = 0, outside the source's Case 2
--   - generalization: Case 2 of a family C containing some c ≠ c0 → no such requirement; reason: if T = ∅ then γpr = 0 and the statement holds vacuously; it specializes to the source's case
--   - generalization: c : ℕ → [0,∞) nondecreasing → c : ℕ → ℝ nonnegative and nondecreasing on the loads k ≥ 1, c(0) free; reason: no quantity reads c(0), and every family of the source satisfies this condition
--   - encoding: c ∈ C \ {c0} → c is nonzero at some load k ≥ 1; reason: c(0) is free in the Lean family
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, proof of Theorem 3, Case 2, display (EC.7), pp.ec3–ec4

import Mathlib
import Definitions.Def_BernoulliPoA_IsCostClass
import Definitions.Def_BernoulliPoA_gammaPr
import Definitions.Def_BernoulliPoA_triples
import Definitions.Def_BernoulliPoA_PsiF
open scoped ENNReal
open scoped NNReal

namespace BernoulliPoA

/-- **Proof of Theorem 3, Case 2: reduction to a finite family, (EC.7).** Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, proof of Theorem 3, Case 2, (EC.7), pp.ec3–ec4: if `c(k) > 0` for all `c ∈ C \ {c₀}` and `k ≥ 1`, then for each
`M < γ_pr(C, q)` there is a finite `F ⊂ T` containing a triple `(c, 1, 0)` such that `Ψ_F(ω) > M` for all `ω ≥ 0` and `Ψ_F` attains its minimum over `ω ≥ 0` at some `ω̄ ≥ 0`.

**Formalization Note** `M` is taken in `ℝ≥0`. A negative `M` is covered by `M = 0` unless `γ_pr = 0`, in which case `T = ∅` and the paper's Case 2 does not arise. The minimum
`γ_pr(F)` of the paper is `PsiF q F hF ω̄`, strictly larger than `M` by the third clause. -/
theorem eq_EC_7 {C : Set (ℕ → ℝ)} (hC : IsCostClass C) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hpos : ∀ c ∈ C, (∃ j, 1 ≤ j ∧ c j ≠ 0) → ∀ k, 1 ≤ k → 0 < c k)
    (M : ℝ≥0) (hM : (M : ℝ≥0∞) < gammaPr C q) :
    ∃ (F : Finset ((ℕ → ℝ) × ℕ × ℕ)) (hF : F.Nonempty),
      (↑F ⊆ triples C) ∧ (∃ c, (c, 1, 0) ∈ F) ∧
      (∀ ω : ℝ, 0 ≤ ω → (M : ℝ) < PsiF q F hF ω) ∧
      ∃ ωbar : ℝ, 0 ≤ ωbar ∧ ∀ ω : ℝ, 0 ≤ ω → PsiF q F hF ωbar ≤ PsiF q F hF ω := by sorry

end BernoulliPoA
