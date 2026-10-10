-- Prove2me | Theorems.Thm_ConleyZehnder_symplectic_joined_one
-- name    : ConleyZehnder.symplectic_joined_one
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T21:23:21.38399+00:00
-- url     : https://prove2.me/theorems/f81802dd-a8b1-4865-b6af-244419ef361b
-- title:
--   The real symplectic group Sp(2n) is path-connected
-- statement:
--   Let $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$ and let $\mathrm{Sp}(2n)=\{A\in\mathbb R^{2n\times 2n}: AJ_0A^{T}=J_0\}$ be the real symplectic group. For every $A\in\mathrm{Sp}(2n)$ there is a continuous path $\gamma:[0,1]\to\mathrm{Sp}(2n)$ with $\gamma(0)=\mathrm{Id}$ and $\gamma(1)=A$. In other words, $\mathrm{Sp}(2n)$ is path-connected.
--
--   This classical fact is used to move a constant conjugating matrix to the identity, as in the naturality property of the Conley–Zehnder index, and more generally whenever an index defined on symplectic paths is compared along deformations.
--
--   Formalization note: `IsSymplectic A` (definition module `ConleyZehnder_Setting`) is membership in Mathlib's `Matrix.symplecticGroup (Fin n) ℝ`, i.e. $AJ_0A^T=J_0$ with $J_0$ = `Matrix.J`; paths are continuous maps `C(unitInterval, Mat n)`.
-- source:
--   Classical; see McDuff-Salamon, Introduction to Symplectic Topology, 3rd ed., Section 2.2; used in Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), Proposition 8 (1)

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- The symplectic group `Sp(ℝ²ⁿ, Ω₀)` is path-connected: every symplectic matrix `A` is
joined to `Id` by a continuous path of symplectic matrices. -/
theorem symplectic_joined_one {n : ℕ} (A : Mat n) (hA : IsSymplectic A) :
    ∃ γ : C(unitInterval, Mat n), γ 0 = 1 ∧ γ 1 = A ∧ ∀ t, IsSymplectic (γ t) := by sorry

end ConleyZehnder
