-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_thickening_sectionTwist_and_nonempty_det_iso
-- name    : AlgebraicGeometry.RelPicard.isLocallyFreeOfRank_pushforward_thickening_sectionTwist_and_nonempty_det_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/e34aaacf-cbe4-5ea7-bcae-cd2fd1204627
-- title:
--   Local freeness and trivial determinant along the n-th section thickening
-- statement:
--   Let $k$ be a field, let $c \colon C \to \operatorname{Spec} k$ be proper and smooth of relative dimension $1$, and let $\varepsilon$ be a section of $c$ over $\operatorname{Spec} k$, i.e. a morphism $\operatorname{Spec} k \to C$ whose composite with $c$ is the identity. Let $t \colon T \to \operatorname{Spec} k$ be locally of finite type, and let $M$ be a rigidified line bundle for $(c,\varepsilon,t)$: a module $M.L$ on the fibre product $C \times_k T$ which is invertible (every point has an open neighbourhood on which the restriction of $M.L$ is isomorphic to the unit module) together with a trivialisation of the pullback of $M.L$ along the induced section `rigSection` $T \to C \times_k T$. Let $r, n \in \mathbb{N}$. Write $\mathcal I$ for `sectionIdeal`, the kernel ideal sheaf data of that section, let $j \colon V(\mathcal I^{\,n}) \hookrightarrow C \times_k T$ be the closed immersion cut out by $\mathcal I^{\,n}$, and let `sectionTwist` of index $r$ be the dual of the module of $\mathcal I^{\,r}$. The assertion is that the module $F := (\mathrm{pr}_2)_* j_* j^* \bigl(M.L \otimes (\mathcal I^{\,r})^{\vee}\bigr)$ on $T$, the pushforward along the second projection $C \times_k T \to T$, is locally free of rank $n$, in the sense that every point of $T$ has an open neighbourhood $U$ with the restriction of $F$ to $U$ isomorphic to the free module on $\mathrm{Fin}\,n$, and that its $n$-th determinant — the sheafified $n$-th exterior power — admits an isomorphism to the unit module $\mathbb{1}_{T}$.
--
--   The module $F$ is the target of the evaluation map $(\mathrm{pr}_2)_* M(r\varepsilon_T) \to F$ on the $n$-th infinitesimal neighbourhood of the section, whose determinant provides the theta section of the relative Picard situation. It is used in the construction of the theta bundle, being cited by [`AlgebraicGeometry.RelPicard.exists_pullbackSection_thetaBundle_eq_zero_iff`](thm.html#AlgebraicGeometry.RelPicard.exists_pullbackSection_thetaBundle_eq_zero_iff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_thickening_sectionTwist_and_nonempty_det_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_ModulesDet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra MonoidalCategory

theorem AlgebraicGeometry.RelPicard.isLocallyFreeOfRank_pushforward_thickening_sectionTwist_and_nonempty_det_iso
    (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType t]
    (M : RigidifiedLineBundle c ε t) (r n : ℕ) :
    Scheme.Modules.IsLocallyFreeOfRank n
        ((Scheme.Modules.pushforward (pullback.snd c t)).obj
          ((Scheme.Modules.pushforward ((sectionIdeal c ε t ^ n).subschemeι)).obj
            ((Scheme.Modules.pullback ((sectionIdeal c ε t ^ n).subschemeι)).obj (M.L ⊗ sectionTwist c ε t r)))) ∧
      Nonempty (Scheme.Modules.det n
          ((Scheme.Modules.pushforward (pullback.snd c t)).obj
            ((Scheme.Modules.pushforward ((sectionIdeal c ε t ^ n).subschemeι)).obj
              ((Scheme.Modules.pullback ((sectionIdeal c ε t ^ n).subschemeι)).obj (M.L ⊗ sectionTwist c ε t r))))
        ≅ 𝟙_ T.Modules) := by sorry
