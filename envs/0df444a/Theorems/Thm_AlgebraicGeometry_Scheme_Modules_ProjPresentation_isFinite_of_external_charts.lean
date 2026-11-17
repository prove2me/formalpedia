-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isFinite_of_external_charts
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.isFinite_of_external_charts
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:13:45.92479+00:00
-- url     : https://prove2.me/theorems/022fd5a0-bbb9-4b68-b6ee-671cbd1deb96
-- title:
--   Exact product-chart descriptions force an external presentation to be finite
-- statement:
--   Let finite projective presentations $P$ on $X$ and $Q$ on $Y$ be given over a field. Let $R$ be a presentation on $X×Y$, and suppose each basic chart of $R$ is exactly the intersection of the pullbacks of the corresponding charts of $P$ and $Q$. Then $$R_{proj}\text{ is finite}.$$ This is the chartwise finiteness criterion for external tensor presentations.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ProjPresentation

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.isFinite_of_external_charts
    {K : Type} [Field K] {X Y : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of K)} {g : Y ⟶ Spec (CommRingCat.of K)}
    {L : X.Modules} {M : Y.Modules} {N N' NR : ℕ}
    (P : L.ProjPresentation f N) (Q : M.ProjPresentation g N')
    (hP : IsFinite P.toProj) (hQ : IsFinite Q.toProj)
    {T : (CategoryTheory.Limits.pullback f g).Modules}
    (R : T.ProjPresentation (pullback.fst f g ≫ f) NR)
    (idx : Fin (NR + 1) → Fin (N + 1) × Fin (N' + 1))
    (hc : ∀ k, R.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X k) =
      pullback.fst f g ⁻¹ᵁ (P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).1)) ⊓
      pullback.snd f g ⁻¹ᵁ (Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).2))) :
    IsFinite R.toProj := by sorry
