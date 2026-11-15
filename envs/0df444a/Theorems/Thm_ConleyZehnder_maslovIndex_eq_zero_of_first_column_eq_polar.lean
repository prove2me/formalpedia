-- Prove2me | Theorems.Thm_ConleyZehnder_maslovIndex_eq_zero_of_first_column_eq_polar
-- name    : ConleyZehnder.maslovIndex_eq_zero_of_first_column_eq_polar
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-14T20:32:33.206196+00:00
-- url     : https://prove2.me/theorems/f14c6868-9ab6-4a2a-acd9-926dd8087e8d
-- title:
--   A symplectic $2\times2$ loop whose first column does not wind has Maslov index zero
-- statement:
--   Let $\gamma:[0,1]\to\mathrm{Sp}(2,\mathbb R)$ be a loop of symplectic $2\times2$ matrices whose first column is $r(t)(\cos\theta(t),\sin\theta(t))^{\mathsf T}$ with $r>0$ and $\theta:[0,1]\to\mathbb R$ continuous and $\theta(1)=\theta(0)$. Then the Maslov index of $\gamma$ is $0$.
--
--   So the Maslov index of a loop in $\mathrm{Sp}(2)$ is detected by the winding of its first column.
--
--   Formalization Note: `Mat 1`, `IsSymplecticLoop` and `maslovIndex` are the platform definitions in `ConleyZehnder` (the Maslov index is the degree of $\hat\rho\circ\gamma$); the first column has entries `γ t (Sum.inl 0) (Sum.inl 0)` and `γ t (Sum.inr 0) (Sum.inl 0)`.
-- source:
--   Standard (Maslov index of loops in Sp(2))

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- Let `γ` be a loop of symplectic `2 × 2` matrices whose first column is
`r t • (cos (θ t), sin (θ t))`, with `r > 0` and `θ` continuous and `θ 1 = θ 0`. Then the
Maslov index of `γ` is `0`. -/
theorem maslovIndex_eq_zero_of_first_column_eq_polar (γ : C(unitInterval, Mat 1))
    (hγ : IsSymplecticLoop γ)
    (θ : unitInterval → ℝ) (hθc : Continuous θ) (hθ1 : θ 1 = θ 0) (r : unitInterval → ℝ)
    (hr : ∀ t, 0 < r t)
    (h0 : ∀ t, γ t (Sum.inl 0) (Sum.inl 0) = r t * Real.cos (θ t))
    (h1 : ∀ t, γ t (Sum.inr 0) (Sum.inl 0) = r t * Real.sin (θ t)) :
    maslovIndex γ = 0 := by
  sorry

end ConleyZehnder
