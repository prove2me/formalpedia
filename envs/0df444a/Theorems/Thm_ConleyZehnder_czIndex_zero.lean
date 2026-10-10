-- Prove2me | Theorems.Thm_ConleyZehnder_czIndex_zero
-- name    : ConleyZehnder.czIndex_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T13:21:59.338609+00:00
-- url     : https://prove2.me/theorems/80b70157-3143-4393-93e5-75a6287177ea
-- title:
--   Zero property of the Conley–Zehnder index
-- statement:
--   Let $\psi\in\mathrm{SP}(n)$ and suppose that for every $s\in(0,1]$ the matrix $\psi(s)$ has no eigenvalue on the unit circle: $\det(\psi(s)-z\,\mathrm{Id})\neq0$ for all $z\in\mathbb{C}$ with $|z|=1$. Then
--   $$\mu_{CZ}(\psi)=0 .$$
-- source:
--   Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), Proposition 8 (3), p. 6; Salamon, Lectures on Floer homology, IAS/Park City Math. Ser. 7 (1999) 143-229, https://doi.org/10.1090/pcms/007/05

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- Gutt, Proposition 8 (3), Zero: if `ψ(s)` has no eigenvalue on the unit circle for
`s > 0`, then `μ_CZ(ψ) = 0`. -/
theorem czIndex_zero {n : ℕ} (ψ : C(unitInterval, Mat n)) (hψ : ψ ∈ SP n)
    (hcirc : ∀ s : unitInterval, 0 < (s : ℝ) → ∀ z : ℂ, ‖z‖ = 1 →
      ((ψ s).map (fun x : ℝ => (x : ℂ)) - z • 1).det ≠ 0) :
    czIndex ψ = 0 := by sorry

end ConleyZehnder
