-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_homeomorph_of_norm_fderiv_sub_id_le
-- name    : FiniteEnergyPlane.exists_homeomorph_of_norm_fderiv_sub_id_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-20T09:16:26.920613+00:00
-- url     : https://prove2.me/theorems/5d96dfbf-66d8-463f-8d05-e2e5586fe620
-- title:
--   A smooth map with derivative uniformly close to the identity is a smooth diffeomorphism
-- statement:
--   Let $E$ be a nontrivial finite-dimensional real normed space and $\psi : E \to E$ a $C^\infty$ map with
--   $$\|D\psi(z) - \mathrm{id}_E\| \le \tfrac12 \quad \text{for every } z \in E$$
--   (operator norm). Then $\psi$ is a homeomorphism of $E$ onto itself and its inverse $\psi^{-1}$ is $C^\infty$.
--
--   Role: a global smooth change of coordinates from a uniform derivative bound, used to turn a map close to the identity in $C^1$ into a reparametrization.
--
--   Formalization note: the conclusion is an `E ≃ₜ E` whose underlying function is literally `ψ`, together with smoothness of its inverse; `∞` is smoothness of every finite order.
-- source:
--   Standard (global inverse function theorem)

import Mathlib

namespace FiniteEnergyPlane

open Set
open scoped ContDiff

/-- A smooth self-map `ψ` of a nontrivial finite-dimensional real normed space whose derivative
satisfies `‖Dψ(z) - id‖ ≤ 1/2` at every point is a homeomorphism (with underlying map `ψ`) whose
inverse is smooth. -/
theorem exists_homeomorph_of_norm_fderiv_sub_id_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] (ψ : E → E) (hψ : ContDiff ℝ ∞ ψ)
    (hD : ∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) :
    ∃ e : E ≃ₜ E, (⇑e = ψ) ∧ ContDiff ℝ ∞ (e.symm : E → E) := by
  sorry

end FiniteEnergyPlane
