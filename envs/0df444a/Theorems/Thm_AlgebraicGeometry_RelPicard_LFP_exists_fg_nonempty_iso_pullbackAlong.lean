-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong
-- name    : AlgebraicGeometry.RelPicard.LFP.exists_fg_nonempty_iso_pullbackAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/5543cba7-b796-5b72-a4e5-f6545a1c3660
-- title:
--   Rigidified line bundles on C_A descend to a finitely generated subalgebra
-- statement:
--   Let $R$ be a commutative ring, let $C$ be a scheme equipped with a two-chart affine open cover $\mathcal V$ (two affine opens $U_0,U_1$ whose union is all of $C$ and whose intersection is again affine), let $c\colon C\to\operatorname{Spec}R$ be a morphism, and let $\varepsilon$ be a section of $c$, that is, a morphism $\operatorname{Spec}R\to C$ whose composite with $c$ is the identity of $\operatorname{Spec}R$. Let $A$ be an $R$-algebra and let $M$ be a rigidified line bundle on the base change of $c$ along $\operatorname{Spec}$ of the structure map $R\to A$: thus $M$ consists of a module $M.L$ on the fibre product $C\times_{\operatorname{Spec}R}\operatorname{Spec}A$ which is invertible in the sense that every point has an open neighbourhood $U$ with the restriction of $M.L$ to $U$ isomorphic to the unit sheaf of $U$, together with a trivialisation of the pullback of $M.L$ along the rigidifying section $\operatorname{Spec}A\to C\times_{\operatorname{Spec}R}\operatorname{Spec}A$ determined by $\varepsilon$. The assertion is that there exist an $R$-subalgebra $A_0\subseteq A$ which is finitely generated as an $R$-algebra and a rigidified line bundle $M_0$ on $C\times_{\operatorname{Spec}R}\operatorname{Spec}A_0$ such that the underlying module of the pullback of $M_0$ along the morphism $C\times_{\operatorname{Spec}R}\operatorname{Spec}A\to C\times_{\operatorname{Spec}R}\operatorname{Spec}A_0$ induced by the inclusion $A_0\hookrightarrow A$ (the identity on $C$ in the first factor) is isomorphic to $M.L$. Only an isomorphism of the underlying modules is asserted; compatibility with the two rigidifications is not part of the conclusion.
--
--   This is the surjectivity half of the statement that the rigidified relative Picard functor of $c\colon C\to\operatorname{Spec}R$ is locally of finite presentation: every rigidified line bundle over a ring $A$ already arises, up to isomorphism of underlying modules, from one of the finitely generated $R$-subalgebras of $A$, whose filtered colimit is $A$. It is used by [`AlgebraicGeometry.RelPicard.isLFPSurj_relPicardPresheaf`](thm.html#AlgebraicGeometry.RelPicard.isLFPSurj_relPicardPresheaf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_AffineLimit
import Definitions.Def_AlgebraicGeometry_RelPicardStageHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.RelPicard.LFP.exists_fg_nonempty_iso_pullbackAlong
    (R : Type u) [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (A : Type u) [CommRing A] [Algebra R A] (M : RigidifiedLineBundle c ε (Scheme.TwoAffineOpenCover.specMap R A)) :
    ∃ (A₀ : Subalgebra R A) (_ : A₀.FG) (M₀ : RigidifiedLineBundle c ε (Scheme.TwoAffineOpenCover.specMap R A₀)),
      Nonempty ((M₀.pullbackAlong (RelPicard.LFP.stageHom R A₀.val)).L ≅ M.L) := by sorry
