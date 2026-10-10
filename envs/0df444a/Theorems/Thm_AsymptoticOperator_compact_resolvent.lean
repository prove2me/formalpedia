-- Prove2me | Theorems.Thm_AsymptoticOperator_compact_resolvent
-- name    : AsymptoticOperator.compact_resolvent
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-09T14:33:05.234857+00:00
-- url     : https://prove2.me/theorems/eaba7a1f-3b87-4dd3-90e5-b3bf832e19aa
-- title:
--   The asymptotic operator has compact resolvent
-- statement:
--   Let $S:S^1\to\mathbb{R}^{2n\times2n}$ be continuous with $S(t)^{\mathsf T}=S(t)$ for all $t$, and let $\mu\in\mathbb{R}$ be such that $A_Sf=\mu f$ has no solution $f\ne0$ in $W^{1,2}$. Then there is a compact bounded operator $R$ on $L^2(S^1,\mathbb{R}^{2n})$ with $R(L^2)\subset W^{1,2}$, $(A_S-\mu)Rg=g$ for all $g\in L^2$, and $R(A_S-\mu)f=f$ for all $f\in W^{1,2}$.
--
--   So $A_S-\mu:W^{1,2}\to L^2$ is bijective with compact inverse.
-- source:
--   Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, §3.2, p. 46 and Lemma 3.16 (the compact resolvent is not stated there explicitly); Hofer-Wysocki-Zehnder, Properties of pseudoholomorphic curves in symplectisations II, GAFA 5 (1995) 270-328, https://doi.org/10.1007/BF01895669, Section 3, p. 285, after equation (35) (n = 1)

import Definitions.Def_AsymptoticOperator_Setting

namespace AsymptoticOperator

open ConleyZehnder

/-- Hofer–Wysocki–Zehnder (GAFA 1995), §3, p. 285 for `n = 1`: if `μ ∈ ℝ` is not an eigenvalue of `A_S`, then `A_S - μ : W^{1,2} → L²` is a
bijection whose inverse is a compact operator on `L²(S¹, ℝ²ⁿ)`. -/
theorem compact_resolvent {n : ℕ} (S : C(UnitAddCircle, Mat n)) (hS : IsSymLoop S) (μ : ℝ)
    (hμ : eigenspace (asymptoticOperator S) μ = ⊥) :
    ∃ R : L2 n →L[ℝ] L2 n, IsCompactOperator R ∧
      (∀ g : L2 n, ∃ h : R g ∈ (asymptoticOperator S).domain,
        (asymptoticOperator S) ⟨R g, h⟩ - μ • R g = g) ∧
      ∀ f : (asymptoticOperator S).domain,
        R ((asymptoticOperator S) f - μ • (f : L2 n)) = f := by sorry

end AsymptoticOperator
