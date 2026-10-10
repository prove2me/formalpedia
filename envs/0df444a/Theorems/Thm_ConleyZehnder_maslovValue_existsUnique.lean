-- Prove2me | Theorems.Thm_ConleyZehnder_maslovValue_existsUnique
-- name    : ConleyZehnder.maslovValue_existsUnique
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T13:20:58.593931+00:00
-- url     : https://prove2.me/theorems/f9c2b78d-9aca-4b9d-bb68-9a22b5b608b0
-- title:
--   The Maslov index $\deg(\hat\rho\circ\varphi)$ of a symplectic loop is well defined
-- statement:
--   Let $\varphi:[0,1]\to\mathrm{Sp}(2n)$ be continuous with $\varphi(0)=\varphi(1)=\mathrm{Id}$. There is exactly one integer $k$ such that some continuous argument $\theta$ of $\hat\rho\circ\varphi$ satisfies
--   $$\theta(1)-\theta(0)=2\pi k .$$
--
--   This integer is the Maslov index $\mu(\varphi)$ appearing in the loop property.
-- source:
--   Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), Proposition 8 (5), p. 7 (Maslov index of a loop); Salamon, Lectures on Floer homology, IAS/Park City Math. Ser. 7 (1999) 143-229, https://doi.org/10.1090/pcms/007/05

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- The Maslov index of a loop is well defined: every loop `φ` of symplectic
matrices at `Id` has a unique degree `deg(ρ̂ ∘ φ)`. -/
theorem maslovValue_existsUnique {n : ℕ} (φ : C(unitInterval, Mat n))
    (hφ : IsSymplecticLoop φ) : ∃! k : ℤ, IsMaslovValue φ k := by sorry

end ConleyZehnder
