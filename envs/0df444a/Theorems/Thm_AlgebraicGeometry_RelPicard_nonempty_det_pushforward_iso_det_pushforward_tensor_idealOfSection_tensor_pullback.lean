-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_det_pushforward_iso_det_pushforward_tensor_idealOfSection_tensor_pullback
-- name    : AlgebraicGeometry.RelPicard.nonempty_det_pushforward_iso_det_pushforward_tensor_idealOfSection_tensor_pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/1a40c260-e3f0-5856-8a3d-d6eb1d51fce8
-- title:
--   Determinant of the direct image along a section
-- statement:
--   Fix a noetherian commutative ring $R$ and a morphism $c : C \to \operatorname{Spec} R$ which is proper and smooth of relative dimension $1$, together with $\varepsilon$, a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Assume the data hypothesis $h\mathfrak{F}$: for every $m_0 \in \mathbb{N}$ there is a `SmoothProperCurve.FiniteMapData` for $c$ and $\varepsilon$ with invariant $m \ge m_0$, that is, a cover of $C$ by two affine opens $U, V$ with $U$ the complement of the image of $\varepsilon$, functions $f \in \Gamma(C,U)$, $g \in \Gamma(C,V)$ which are mutually inverse on $U \cap V = C_f = C_g$, with $\Gamma(C,U)$ finite over $R[f]$ and $\Gamma(C,V)$ finite over $R[g]$, and all level sets of $f$ over local $R$-algebras finite free of rank $m$. Let $t : T \to \operatorname{Spec} R$ be locally of finite type, write $\pi = \mathrm{pullback.snd}\, c\, t : C_T \to T$, and let $p : T \to C_T$ satisfy $p$ followed by $\pi$ equals $\mathbb{1}_T$. Let $F$ be a module on $C_T$ which is invertible in the sense that every point has an open neighbourhood $U$ with the restriction of $F$ to $U$ isomorphic to the unit sheaf, and let $n \in \mathbb{N}$. Two fibrewise hypotheses are assumed: for every field $k$, every $s : \operatorname{Spec} k \to T$ and every cover of the fibre $C_T \times_T \operatorname{Spec} k$ by two affine opens with affine intersection, the two-chart Čech complex (sections over the two charts and over their intersection, with the difference map) of the pullback of $F \otimes \mathcal{I}_p$ to the fibre has vanishing $H^1$ (it is a subsingleton) and $H^0$ of $k$-dimension $n$; and the same complex for the pullback of $F$ has vanishing $H^1$ and $H^0$ of $k$-dimension $n+1$. Here $\mathcal{I}_p =$ `p.ker.module` is the kernel of the map from the unit sheaf to the pushforward of the unit sheaf along the closed immersion cut out by $p$. The conclusion is that the type of isomorphisms $$\textstyle\bigwedge^{n+1} \pi_* F \;\cong\; \bigl(\bigwedge^{n} \pi_*(F \otimes \mathcal{I}_p)\bigr) \otimes p^* F$$ of modules on $T$ is nonempty, the exterior powers being the sheafified exterior powers of `Scheme.Modules.det`.
--
--   This is the determinant computation attached to the point sequence $0 \to \pi_*(F \otimes \mathcal{I}_p) \to \pi_* F \to p^* F \to 0$ on a relative smooth proper curve, the elementary Picard-bundle identity underlying the theorem of the square for theta bundles on Jacobians. It is used in the construction of the theta bundle for the relative Picard functor, where it is invoked in the comparison of the theta bundle of $F$ with that of $F$ twisted by a point minus the basepoint.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_nonempty_det_pushforward_iso_det_pushforward_tensor_idealOfSection_tensor_pullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra MonoidalCategory
  AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.RelPicard.nonempty_det_pushforward_iso_det_pushforward_tensor_idealOfSection_tensor_pullback
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (p : T ⟶ pullback c t) (hp : p ≫ pullback.snd c t = 𝟙 T)
    (F : (pullback c t).Modules) (hF : Scheme.Modules.IsInvertible F) (n : ℕ)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (F ⊗ p.ker.module))).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (F ⊗ p.ker.module))).H0 = n)
    (hfib' : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H0 = n + 1) :
    Nonempty (Scheme.Modules.det (n + 1) ((Scheme.Modules.pushforward (pullback.snd c t)).obj F) ≅
      Scheme.Modules.det n ((Scheme.Modules.pushforward (pullback.snd c t)).obj (F ⊗ p.ker.module)) ⊗
        (Scheme.Modules.pullback p).obj F) := by sorry
