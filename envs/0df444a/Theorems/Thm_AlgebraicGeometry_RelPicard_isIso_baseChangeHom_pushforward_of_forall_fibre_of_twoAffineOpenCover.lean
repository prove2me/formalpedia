-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isIso_baseChangeHom_pushforward_of_forall_fibre_of_twoAffineOpenCover
-- name    : AlgebraicGeometry.RelPicard.isIso_baseChangeHom_pushforward_of_forall_fibre_of_twoAffineOpenCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/d7927df8-9876-5f64-b209-acc0e4592f5e
-- title:
--   Cohomology and base change for a proper flat family
-- statement:
--   Let $R$ be a Noetherian commutative ring, let $c : C \to \operatorname{Spec} R$ be a proper flat morphism of schemes, and let $\mathcal V$ be a two-affine open cover of $C$, that is, affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine. Let $t : T \to \operatorname{Spec} R$ be locally of finite type, let $t' : T' \to \operatorname{Spec} R$ be arbitrary, and let $\psi$ be a morphism $T' \to T$ with $\psi \circ t' = t$ as morphisms over $\operatorname{Spec} R$ (an element of `SchemeHomOver t' t`). Let $F$ be a module on $C \times_{\operatorname{Spec} R} T$ which is invertible in the sense that every point has an open neighbourhood $U$ on which the restriction of $F$ is isomorphic to the unit sheaf of modules of $U$, and let $n$ be a natural number. Assume that for every field $k$, every $s : \operatorname{Spec} k \to T$ and every two-affine open cover $\mathcal W$ of the fibre $(C \times_{\operatorname{Spec} R} T) \times_T \operatorname{Spec} k$, the two-term Čech complex of the pullback of $F$ to that fibre, taken with respect to $\mathcal W$ and the structural morphism to $\operatorname{Spec} k$, has $H^1$ (the cokernel of $(m_0,m_1) \mapsto r_1 m_1 - r_0 m_0$ on $\Gamma(U_0) \times \Gamma(U_1) \to \Gamma(U_0 \sqcap U_1)$) a subsingleton, and $H^0$ (the kernel of that map) of $k$-dimension exactly $n$. Then the base-change morphism $\psi^{*}(\mathrm{pr}_2)_{*}F \to (\mathrm{pr}_2')_{*}\bigl((1 \times \psi)^{*}F\bigr)$ attached to the commuting square formed by the second projections of $C \times_{\operatorname{Spec} R} T$ and $C \times_{\operatorname{Spec} R} T'$ and the map induced by $\psi$ is an isomorphism.
--
--   This is the cohomology-and-base-change theorem in the form used for relative Picard functors: when the first Čech cohomology vanishes and the zeroth has constant rank $n$ on all field-valued fibres, formation of the direct image of an invertible module commutes with arbitrary base change $T' \to T$ over $\operatorname{Spec} R$. It is applied to show that the relevant pullback of a counit component is non-zero in the construction of line bundles on relative Picard schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isIso_baseChangeHom_pushforward_of_forall_fibre_of_twoAffineOpenCover.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_ModulesBaseChangeHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra MonoidalCategory
  AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.RelPicard.isIso_baseChangeHom_pushforward_of_forall_fibre_of_twoAffineOpenCover
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover)
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} [LocallyOfFiniteType t]
    (ψ : SchemeHomOver t' t) (F : (pullback c t).Modules) (hF : Scheme.Modules.IsInvertible F) (n : ℕ)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H0 = n) :
    IsIso (Scheme.Modules.baseChangeHom
      (RelPicard.BaseChange.baseChangeSnd_snd' (cc := c) (ψ := ψ)) F) := by sorry
