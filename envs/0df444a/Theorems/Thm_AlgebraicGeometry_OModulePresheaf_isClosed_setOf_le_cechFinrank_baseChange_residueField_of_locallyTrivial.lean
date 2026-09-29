-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isClosed_setOf_le_cechFinrank_baseChange_residueField_of_locallyTrivial
-- name    : AlgebraicGeometry.OModulePresheaf.isClosed_setOf_le_cechFinrank_baseChange_residueField_of_locallyTrivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/3ac0179c-e086-53de-a597-3e96481f6186
-- title:
--   Upper semicontinuity of fibrewise Čech ranks, residue-field form
-- statement:
--   Let $S$ be a noetherian commutative ring, $X$ a scheme and $\pi : X \to \operatorname{Spec} S$ a morphism that is proper and flat, and let $M$ be an $\mathcal O_X$-module (an object of `X.Modules`). Assume `htriv`: every point of $X$ has an open neighbourhood $U$ for which the pullback of $M$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules over the structure sheaf of $U$, i.e. $M$ is locally isomorphic to $\mathcal O_X$. Let $\mathcal U$ be an `OrderedAffineCover` of $X$: a finite linearly ordered index set together with affine opens whose supremum is $\top$. Fix $i, r \in \mathbb N$. For a prime $q$ of $S$ with residue field $\kappa(q)$, form the fibre product of $\pi$ with $\operatorname{Spec}\kappa(q) \to \operatorname{Spec} S$, regard it as a scheme over $\kappa(q)$ via the second projection, pull $M$ back along the first projection, and take the cover obtained by pulling back each member of $\mathcal U$ along the first projection. The conclusion is that the set of primes $q$ with $r \le \mathrm{cechFinrank}$ in degree $i$ of the resulting presheaf of sections is closed in $\operatorname{Spec} S$; here $\mathrm{cechFinrank}$ in degree $0$ is $\dim_{\kappa(q)}$ of the kernel of the first Čech differential, and in degree $j+1$ is $\dim_{\kappa(q)}$ of $\ker d^{j+1}$ modulo the image of $d^{j}$.
--
--   This is the residue-field form, in every degree, of the upper semicontinuity of the fibrewise cohomology ranks in a proper flat family (EGA III 7.7.5; Hartshorne III.12.8; Mumford, Abelian Varieties §5), stated for the Čech complex of a finite ordered affine cover and an invertible module. It is used in the study of good reduction of Jacobians, to produce a prime at which the geometric fibres have no nonzero global sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_isClosed_setOf_le_cechFinrank_baseChange_residueField_of_locallyTrivial.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.OModulePresheaf.isClosed_setOf_le_cechFinrank_baseChange_residueField_of_locallyTrivial
    {S : Type u} [CommRing S] [IsNoetherianRing S] {X : Scheme.{u}} (π : X ⟶ Spec (.of S))
    [IsProper π] [Flat π] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (𝒰 : X.OrderedAffineCover) (i r : ℕ) :
    IsClosed {q : PrimeSpectrum S | r ≤
      (OModulePresheaf.ofModules
          (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap S q.asIdeal.ResidueField))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap S q.asIdeal.ResidueField))).obj M)).cechFinrank
        (𝒰.baseChange π q.asIdeal.ResidueField) i} := by sorry
