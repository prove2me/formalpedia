-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIntegral_genericFiber_of_isDominant
-- name    : AlgebraicGeometry.isIntegral_genericFiber_of_isDominant
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-23T20:25:04.337197+00:00
-- url     : https://prove2.me/theorems/fd773659-17a0-42e8-8f33-baf6f63e161d
-- title:
--   The generic fibre of a dominant morphism of integral schemes is integral
-- statement:
--   Let $f:X\to Y$ be a dominant morphism of integral schemes, and suppose that $X$ is locally noetherian. If $\eta$ is the generic point of $Y$, then its scheme-theoretic generic fibre is integral:
--   $$X_\eta=X\times_Y\operatorname{Spec}\kappa(\eta)\quad\text{is integral}.$$
--   No properness, finite-type, characteristic or algebraic-closure hypothesis is imposed on $f$ or $Y$. The local noetherian hypothesis on $X$ is retained in this formulation.
--
--   This supplies an actual integral generic-fibre scheme for passing from a dominant projection and its function-field parameters to a curve over the generic-point residue field. **Formalization Note.** The statement uses the scheme-theoretic fibre and the generic point of the original integral base. It includes nonemptiness and reducedness, in addition to irreducibility.
-- source:
--   Consequence of Stacks Project, Section 37.24 (Generic fibres), Lemma 37.24.6 on reducedness of generic fibres, https://stacks.math.columbia.edu/tag/054V and https://stacks.math.columbia.edu/tag/054Z , together with the generic-point behavior of a dominant morphism of irreducible schemes and the fibre embedding. The present derived formulation retains local noetherianness of the integral source to use the flat, geometrically reduced base-change criterion for reducedness; no finite-type or properness assumption is added. Supporting generic-fibre infrastructure for the projection stages of A. J. de Jong, Smoothness, semi-stability and alterations (1996), Sections 4.11-4.12, https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf .

import Mathlib
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

theorem AlgebraicGeometry.isIntegral_genericFiber_of_isDominant
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] : IsIntegral (f.fiber (genericPoint Y)) := by sorry
