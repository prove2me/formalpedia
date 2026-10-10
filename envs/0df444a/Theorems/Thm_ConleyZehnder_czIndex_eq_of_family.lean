-- Prove2me | Theorems.Thm_ConleyZehnder_czIndex_eq_of_family
-- name    : ConleyZehnder.czIndex_eq_of_family
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T21:23:25.336592+00:00
-- url     : https://prove2.me/theorems/89960756-4e91-4ffa-bcc3-ff961f575479
-- title:
--   The Conley–Zehnder index is constant along continuous families of paths in SP(n)
-- statement:
--   Let $\mathrm{SP}(n)$ be the set of continuous paths $\psi:[0,1]\to\mathrm{Sp}(2n)$ with $\psi(0)=\mathrm{Id}$ and $\det(\mathrm{Id}-\psi(1))\neq 0$ (Gutt, Definition 4), and let $\mu_{CZ}$ be the Conley–Zehnder index (Gutt, Definition 7 and Corollary 12).
--
--   Let $H:[0,1]\times[0,1]\to\mathbb R^{2n\times 2n}$ be continuous such that for every $s$ the path $t\mapsto H(s,t)$ lies in $\mathrm{SP}(n)$: every $H(s,t)$ is symplectic, $H(s,0)=\mathrm{Id}$ and $1$ is not an eigenvalue of $H(s,1)$. Then
--   $$\mu_{CZ}\bigl(H(0,\cdot)\bigr)=\mu_{CZ}\bigl(H(1,\cdot)\bigr).$$
--
--   So $\mu_{CZ}$ is invariant under continuous deformations inside $\mathrm{SP}(n)$; the endpoint $H(s,1)$ is allowed to move within the matrices without eigenvalue $1$. This is the deformation form of the homotopy property and is reused for the naturality and homotopy properties of the index.
--
--   Formalization note: `IsSymplectic`, `czIndex` and `Mat n` come from the definition module `ConleyZehnder_Setting`. The two end paths are passed as `ψ₀ ψ₁ : C(unitInterval, Mat n)` with `ψ₀ t = H (0, t)` and `ψ₁ t = H (1, t)`.
-- source:
--   Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), Proposition 8 (2) (homotopy), deformation form

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- `μ_CZ` is constant along a continuous one-parameter family `s ↦ H (s, ·)` of paths in
`SP(n)`: if every `H (s, t)` is symplectic, `H (s, 0) = Id` and `1` is not an eigenvalue of
`H (s, 1)`, then the paths `H (0, ·)` and `H (1, ·)` have the same Conley–Zehnder index. -/
theorem czIndex_eq_of_family {n : ℕ} (H : C(unitInterval × unitInterval, Mat n))
    (hH : ∀ s t, IsSymplectic (H (s, t))) (h0 : ∀ s, H (s, 0) = 1)
    (h1 : ∀ s, (1 - H (s, 1)).det ≠ 0)
    (ψ₀ ψ₁ : C(unitInterval, Mat n)) (hψ₀ : ∀ t, ψ₀ t = H (0, t))
    (hψ₁ : ∀ t, ψ₁ t = H (1, t)) :
    czIndex ψ₁ = czIndex ψ₀ := by sorry

end ConleyZehnder
