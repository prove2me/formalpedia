-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_fibre_eulerChar_eq_and_isClopen_setOf_fibre_eulerChar_eq
-- name    : AlgebraicGeometry.RelPicard.exists_fibre_eulerChar_eq_and_isClopen_setOf_fibre_eulerChar_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/41279e30-73b1-5657-9c42-a8ffaee3e782
-- title:
--   Fibrewise Euler characteristic is well defined and locally constant
-- statement:
--   Let $R$ be a Noetherian commutative ring, let $c\colon C\to\operatorname{Spec}R$ be a proper flat morphism of schemes, and suppose $C$ carries a two-affine open cover $\mathcal V$, that is, two affine opens $U_0,U_1$ with $U_0\sqcup U_1=\top$ and $U_0\cap U_1$ affine. Let $t\colon T\to\operatorname{Spec}R$ be locally of finite type and let $M$ be a module on the fibre product $C\times_{\operatorname{Spec}R}T$ which is invertible in the sense that every point has an open neighbourhood $U$ on which the restriction of $M$ is isomorphic to the unit sheaf of modules of $U$. For a field $k$ and a morphism $s\colon\operatorname{Spec}k\to T$, write $F_s$ for the pullback $(C\times_{\operatorname{Spec}R}T)\times_T\operatorname{Spec}k$ with its projection `fibreAt` to $\operatorname{Spec}k$ and $M_s$ for the pullback `fibreModule` of $M$ to $F_s$; for a two-affine open cover $\mathcal W$ of $F_s$ the associated two-chart Čech data have $M_0=\Gamma(M_s,W_0)$, $M_1=\Gamma(M_s,W_1)$, $M_{01}=\Gamma(M_s,W_0\cap W_1)$ and differential $(-r_0)\oplus r_1$, with $H^0$ its kernel and $H^1$ the quotient of $M_{01}$ by its range, both $k$-modules. The conclusion is twofold: first, for every point $x$ of $T$ there is an integer $e$ such that for every field $k$, every $s\colon\operatorname{Spec}k\to T$ carrying the closed point to $x$, and every two-affine open cover $\mathcal W$ of $F_s$, one has $\dim_k H^0-\dim_k H^1=e$; second, for every integer $e$ the set of $x\in T$ satisfying this condition is open and closed in $T$.
--
--   This is the statement that the Euler characteristic $\chi=h^0-h^1$ of the fibres of an invertible module in a proper flat family is independent of all choices at a given point of the base and is locally constant there, in the two-chart Čech formulation used throughout this development. It is invoked in the comparison of fibres of glued curves over a connected base and in the computation of $h^0-h^1$ on the special fibre of a two-chart integral model of $X_1(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_fibre_eulerChar_eq_and_isClopen_setOf_fibre_eulerChar_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.RelPicard

universe u

theorem AlgebraicGeometry.RelPicard.exists_fibre_eulerChar_eq_and_isClopen_setOf_fibre_eulerChar_eq
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M) :
    (∀ x : T, ∃ e : ℤ, ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      s.base (IsLocalRing.closedPoint k) = x →
        ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
          (Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 : ℤ) -
            Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 = e) ∧
    ∀ e : ℤ, IsClopen {x : T | ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      s.base (IsLocalRing.closedPoint k) = x →
        ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
          (Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 : ℤ) -
            Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 = e} := by sorry
