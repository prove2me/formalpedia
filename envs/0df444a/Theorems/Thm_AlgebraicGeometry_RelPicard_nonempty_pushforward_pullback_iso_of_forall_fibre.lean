-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pushforward_pullback_iso_of_forall_fibre
-- name    : AlgebraicGeometry.RelPicard.nonempty_pushforward_pullback_iso_of_forall_fibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/87bd6a2b-f8c5-5025-973b-738a925303a6
-- title:
--   Degree-zero base change for a fibrewise acyclic invertible sheaf
-- statement:
--   Let $R$ be a Noetherian commutative ring, let $c : C \to \operatorname{Spec} R$ be proper and smooth of relative dimension $1$, and let $\varepsilon$ be a section, i.e. a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Assume that for every $m_0 \in \mathbb{N}$ there is finite map data $\mathfrak{F}$ for $(c,\varepsilon)$ with $m_0 \le \mathfrak{F}.m$: a pair of affine opens $U, V$ covering $C$ with $U$ the complement of the image of $\varepsilon$, functions $f \in \Gamma(C,U)$, $g \in \Gamma(C,V)$ whose basic opens both equal $U \cap V$ and whose restrictions there multiply to $1$, making $\Gamma(C,U)$ and $\Gamma(C,V)$ finite over $R[X]$, and such that over every local $R$-algebra $S$ and every $s \in S$ the level set $S \otimes_R \Gamma(C,U)/(1 \otimes f - s \otimes 1)$ is finite free of rank $\mathfrak{F}.m$. Let $t : T \to \operatorname{Spec} R$ be locally of finite type, $t' : T' \to \operatorname{Spec} R$ arbitrary, and $\psi$ a morphism $T' \to T$ over $\operatorname{Spec} R$. Let $F$ be a sheaf of modules on $C \times_R T$ that is invertible in the sense that each point of $C \times_R T$ has an open neighbourhood on which $F$ restricts to a sheaf isomorphic to the unit sheaf of modules, and let $n \in \mathbb{N}$. Assume that for every field $k$, every $s : \operatorname{Spec} k \to T$ and every two-affine open cover $\mathcal{W}$ of the fibre $(C \times_R T) \times_T \operatorname{Spec} k$, the associated two-chart Čech complex of the pulled-back module over $k$ has vanishing (subsingleton) $H^1$ and $\dim_k H^0 = n$, where $H^0$ is the kernel and $H^1$ the cokernel of the Čech differential. Then there exists an isomorphism of sheaves of modules on $C \times_R T'$ — strictly, the type of such isomorphisms is nonempty — between the pushforward along $\operatorname{pr}_2 : C \times_R T' \to T'$ of the pullback of $F$ along the induced map $C \times_R T' \to C \times_R T$ (identity on $C$, $\psi$ on the base), and the pullback along $\psi$ of the pushforward of $F$ along $\operatorname{pr}_2 : C \times_R T \to T$.
--
--   This is the base-change half of cohomology and base change in degree $0$ for a fibrewise acyclic invertible sheaf on a smooth proper relative curve: formation of the direct image commutes with arbitrary base change $T' \to T$. It is used to identify the theta bundle of a base-changed family of line bundles with the pullback of the theta bundle, and is cited by [`AlgebraicGeometry.RelPicard.nonempty_pullback_thetaBundle_iso`](thm.html#AlgebraicGeometry.RelPicard.nonempty_pullback_thetaBundle_iso).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_nonempty_pushforward_pullback_iso_of_forall_fibre.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra MonoidalCategory
  AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.RelPicard.nonempty_pushforward_pullback_iso_of_forall_fibre
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} [LocallyOfFiniteType t]
    (ψ : SchemeHomOver t' t) (F : (pullback c t).Modules) (hF : Scheme.Modules.IsInvertible F) (n : ℕ)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H0 = n) :
    Nonempty ((Scheme.Modules.pushforward (pullback.snd c t')).obj ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj F) ≅
      (Scheme.Modules.pullback ψ.1).obj ((Scheme.Modules.pushforward (pullback.snd c t)).obj F)) := by sorry
