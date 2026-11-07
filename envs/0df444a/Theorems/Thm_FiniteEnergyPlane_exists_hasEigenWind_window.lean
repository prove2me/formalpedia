-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_hasEigenWind_window
-- name    : FiniteEnergyPlane.exists_hasEigenWind_window
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T14:08:06.148231+00:00
-- url     : https://prove2.me/theorems/a9587d76-028e-4d0c-bd88-0776b3318008
-- title:
--   A weight below zero for the asymptotic operator of an orbit of index at least three
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$ be a strictly star-shaped level with a compatible complex structure $J$ on the contact planes, and let $P$ be a periodic Reeb orbit, possibly degenerate, whose Conley–Zehnder index is at least $3$ (`P.IsCZAtLeast 3`).
--
--   Then there is $\delta < 0$ which is not an eigenvalue of the asymptotic operator $A_P$, such that every eigenvalue $\mu < \delta$ of $A_P$ has winding number at most $1$ and every eigenvalue $\mu > \delta$ has winding number at least $2$, in the global frame of $\xi$.
--
--   **Role.** This is the exponential weight used for operators along fast finite-energy planes asymptotic to $P$, in the setting of Hryniewicz (Trans. AMS 2012), Section 6. It does not require $P$ to be nondegenerate.
--
--   **Formalization Note.** "Eigenvalue $\mu$ with winding number $k$" is `HasEigenWind J P μ k`, and "not an eigenvalue" is `∀ v, ¬ IsAsymptoticEigen J P δ v`.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Section 6 (the weight δ of (87))

import Definitions.Def_FiniteEnergyPlane_Compactness

namespace FiniteEnergyPlane

/-- Let `P` be a periodic Reeb orbit, possibly degenerate, with Conley–Zehnder index at least `3`.
Then there is `δ < 0` which is not an eigenvalue of the asymptotic operator `A_P`, such that every
eigenvalue below `δ` has winding number at most `1` and every eigenvalue above `δ` has winding
number at least `2`, in the global frame of `ξ`. -/
theorem exists_hasEigenWind_window (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)
    (hcz : P.IsCZAtLeast 3) :
    ∃ δ < 0, (∀ v, ¬ IsAsymptoticEigen J P δ v) ∧
      ∀ (μ : ℝ) (k : ℤ), HasEigenWind J P μ k → (μ < δ ∧ k ≤ 1) ∨ (δ < μ ∧ 2 ≤ k) := by
  sorry

end FiniteEnergyPlane
