-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening
-- name    : AlgebraicGeometry.RelPicard.shortExact_map_pushforward_thickening
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/3d976b37-1644-5ab6-92f8-801bb0f1e193
-- title:
--   Pushforward of a thickening sequence along a relative curve
-- statement:
--   Let $k$ be a field and let $c \colon C \to \operatorname{Spec} k$ be proper and smooth of relative dimension $1$, and let $\varepsilon$ be an element of $\mathrm{SchemeHomOver}\,(\mathbf 1_{\operatorname{Spec} k})\,c$, that is, a morphism $\operatorname{Spec} k \to C$ whose composite with $c$ is the identity. Let $t \colon T \to \operatorname{Spec} k$ be locally of finite type, write $\operatorname{pullback} c\, t$ for $C \times_k T$, and let $H$ be a module on $C \times_k T$ which is invertible in the sense that every point has an open neighbourhood $U$ on which the restriction of $H$ along $U \hookrightarrow C\times_k T$ is isomorphic to the unit sheaf of modules. Let $m$ be a natural number and put $\mathcal I = \mathrm{sectionIdeal}\, c\, \varepsilon\, t$, the kernel ideal sheaf datum of the section $\mathrm{rigSection}\, c\, t\, \varepsilon \colon T \to C\times_k T$ determined by $t \circ \varepsilon$ and $\mathbf 1_T$. Let $S$ be a short complex of modules on $C\times_k T$ which is short exact, and suppose given isomorphisms $e_2$ from $S.X_2$ to the pushforward along the closed immersion of the subscheme of $\mathcal I^{m+1}$ of the pullback of $H$ to that subscheme, and $e_3$ from $S.X_3$ to the corresponding pushforward of the pullback of $H$ along the closed immersion of the subscheme of $\mathcal I$. Assume the pinning hypothesis that the unit of the pullback–pushforward adjunction at $H$ for the closed immersion attached to $\mathcal I^{m+1}$, followed by $e_2^{-1}$, then $S.g$, then $e_3$, equals the unit of the adjunction at $H$ for the closed immersion attached to $\mathcal I$. Then the short complex obtained from $S$ by applying the pushforward of modules along the projection $\mathrm{pullback.snd}\, c\, t \colon C\times_k T \to T$ is short exact.
--
--   This is the exactness of the direct image to the base of the restriction sequence relating the $(m+1)$-st and first thickenings of a section of a smooth proper relative curve, the sequence being recognised by the two adjunction units rather than by its construction. It is used in the study of pushforwards of twists along the section, namely by [`AlgebraicGeometry.RelPicard.isLocallyFreeOfRank_pushforward_thickening_sectionTwist_and_nonempty_det_iso`](thm.html#AlgebraicGeometry.RelPicard.isLocallyFreeOfRank_pushforward_thickening_sectionTwist_and_nonempty_det_iso), in the infrastructure for the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra MonoidalCategory

theorem AlgebraicGeometry.RelPicard.shortExact_map_pushforward_thickening
    (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType t]
    (H : (pullback c t).Modules) (hH : Scheme.Modules.IsInvertible H) (m : ℕ)
    (S : ShortComplex (pullback c t).Modules) (hS : S.ShortExact)
    (e₂ : S.X₂ ≅ (Scheme.Modules.pushforward ((sectionIdeal c ε t ^ (m + 1)).subschemeι)).obj
        ((Scheme.Modules.pullback ((sectionIdeal c ε t ^ (m + 1)).subschemeι)).obj H))
    (e₃ : S.X₃ ≅ (Scheme.Modules.pushforward (sectionIdeal c ε t).subschemeι).obj
        ((Scheme.Modules.pullback (sectionIdeal c ε t).subschemeι).obj H))
    (hpin : (Scheme.Modules.pullbackPushforwardAdjunction ((sectionIdeal c ε t ^ (m + 1)).subschemeι)).unit.app H ≫
        e₂.inv ≫ S.g ≫ e₃.hom
      = (Scheme.Modules.pullbackPushforwardAdjunction (sectionIdeal c ε t).subschemeι).unit.app H) :
    (S.map (Scheme.Modules.pushforward (pullback.snd c t))).ShortExact := by sorry
