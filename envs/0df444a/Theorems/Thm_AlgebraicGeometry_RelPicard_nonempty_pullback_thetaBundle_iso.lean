-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_thetaBundle_iso
-- name    : AlgebraicGeometry.RelPicard.nonempty_pullback_thetaBundle_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/4be05a84-f73e-5659-98d9-527fc2e5e273
-- title:
--   Base change of the theta bundle along ψ: T'→ T
-- statement:
--   Let $R$ be a Noetherian commutative ring and let $c\colon C\to\operatorname{Spec}R$ be proper and smooth of relative dimension $1$, equipped with a section $\varepsilon$ (an element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c`, i.e. a morphism $\operatorname{Spec}R\to C$ splitting $c$), and assume that for every $m_0\in\mathbb{N}$ there is an instance of the project's structure `SmoothProperCurve.FiniteMapData` for $(c,\varepsilon)$ with invariant $m\ge m_0$ (two affine charts covering $C$, the first being the complement of the image of $\varepsilon$, glued by mutually inverse functions $f,g$ on the overlap, finite of degree $m$ over $R$ in the sense recorded there). Let $t\colon T\to\operatorname{Spec}R$ be locally of finite type and $t'\colon T'\to\operatorname{Spec}R$ arbitrary, and let $M$ be a rigidified line bundle on $C\times_R T$: an invertible module $M.L$ on `pullback c t` whose restriction along the rigidifying section is isomorphic to the unit. Fix $r,n\in\mathbb{N}$ and assume the fibrewise hypothesis: for every field $k$, every $k$-point $s\colon\operatorname{Spec}k\to T$ and every two-affine open cover $\mathcal{W}$ of the fibre $\,$`pullback (pullback.snd c t) s`, the two-chart Čech complex of the pullback of $M.L\otimes$`sectionTwist c ε t r` (the dual of the $r$-th power of the section ideal, i.e. $\mathcal{O}(r\varepsilon_T)$) for that cover has vanishing $H^1$ (a subsingleton) and $H^0$ of $k$-dimension $n$. Finally let $\psi\colon T'\to T$ satisfy $\psi\circ t=t'$, let $M'$ be a rigidified line bundle on $C\times_R T'$, and let $e$ be an isomorphism of $M'.L$ with the underlying module of the pullback of $M$ along $\psi$. The conclusion is that the set of isomorphisms between $\psi^{*}\,$`thetaBundle c ε t M r n` and `thetaBundle c ε t' M' r n` is nonempty, where `thetaBundle` denotes the dual of the $n$-th determinant of the Picard bundle $(\mathrm{pr}_2)_*(M.L\otimes\mathcal{O}(r\varepsilon))$; no particular isomorphism is specified.
--
--   This is the statement that formation of the theta line bundle $\Theta_{r,n}(M)=\bigl(\det{}_n (\mathrm{pr}_2)_*(M\otimes\mathcal{O}(r\varepsilon_T))\bigr)^{\vee}$ on the parameter scheme commutes with base change $T'\to T$, and depends on $M$ only through the isomorphism class of its underlying invertible module. It feeds the construction of the theta polarisation on the relative Picard scheme, and is used in the comparison of theta bundles along the two projections of a base change and under translation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_thetaBundle_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra MonoidalCategory
  AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.RelPicard.nonempty_pullback_thetaBundle_iso
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} [LocallyOfFiniteType t]
    (M : RigidifiedLineBundle c ε t) (r n : ℕ)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c ε t r))).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c ε t r))).H0 = n)
    (ψ : SchemeHomOver t' t) (M' : RigidifiedLineBundle c ε t') (e : M'.L ≅ (M.pullbackAlong ψ).L) :
    Nonempty ((Scheme.Modules.pullback ψ.1).obj (thetaBundle c ε t M r n) ≅ thetaBundle c ε t' M' r n) := by sorry
