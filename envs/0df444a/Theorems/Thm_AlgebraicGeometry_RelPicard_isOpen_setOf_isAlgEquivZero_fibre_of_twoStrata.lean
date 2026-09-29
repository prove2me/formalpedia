-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isOpen_setOf_isAlgEquivZero_fibre_of_twoStrata
-- name    : AlgebraicGeometry.RelPicard.isOpen_setOf_isAlgEquivZero_fibre_of_twoStrata
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/745aae62-0c28-5ae4-875e-6cd4b56e3ccb
-- title:
--   Openness of the fibrewise algebraic-equivalence locus, two-strata form
-- statement:
--   Let $R$ be a Noetherian commutative ring, let $c\colon C\to\operatorname{Spec}R$ be proper and flat, let $\mathcal V$ be a two-affine open cover of $C$ (two affine opens whose union is $C$ and whose intersection is affine), let $\varepsilon$ be a section of $c$ over the identity of $\operatorname{Spec}R$, and let $Z_0\subseteq\operatorname{Spec}R$ be closed. For a scheme $T$ with $t\colon T\to\operatorname{Spec}R$ locally of finite type, a rigidified line bundle $L$ on $C\times_RT$ (an invertible module together with a trivialisation of its pullback along the section $\varepsilon$), an algebraically closed field $k$ and $s\colon\operatorname{Spec}k\to T$, write $\mathrm{CUT}$ for the predicate `IsAlgEquivZero` applied to the fibre $C\times_RT\times_Ts\to\operatorname{Spec}k$ and the pullback of $L$ to it, namely: there are $h\colon T'\to\operatorname{Spec}k$ locally of finite type and geometrically integral, an invertible module $M$ on the fibre product along $h$, and two sections $t_0,t_1$ of $h$, such that the pullback of $M$ along $t_0$ is isomorphic to the unit module and its pullback along $t_1$ is isomorphic to the given fibre module. Three hypotheses are assumed, for all such $(T,t,L)$, $k$ and $s$: (i) if $\mathrm{CUT}$ holds at $s$ then, for every two-affine open cover $\mathcal W$ of the fibre, the two-chart Čech index $\dim_k H^0-\dim_k H^1$ (kernel and cokernel of the Čech differential) of the fibre of $L$ equals that of the unit module; (ii) if $t(s(\text{closed point}))\notin Z_0$ then, for every such $\mathcal W$, that equality of indices implies $\mathrm{CUT}$ at $s$; (iii) there is an open $U\subseteq T$ with $U\cap t^{-1}(Z_0)$ equal to the set of $x\in t^{-1}(Z_0)$ at which $\mathrm{CUT}$ holds for every algebraically closed $k$ and every $s$ with image $\{x\}$. The conclusion is that for every $T$, every locally of finite type $t\colon T\to\operatorname{Spec}R$ and every rigidified line bundle $L$ on $C\times_RT$, the set of $x\in T$ such that $\mathrm{CUT}$ holds for all algebraically closed $k$ and all $s\colon\operatorname{Spec}k\to T$ with image $\{x\}$ is open.
--
--   This is the openness of the locus where a line bundle on a flat proper curve over a base is fibrewise algebraically equivalent to zero, in a form that splits the base into the degeneration stratum $Z_0$, where openness is imported as a hypothesis, and its complement, where algebraic equivalence to zero is detected by constancy of the two-chart Čech Euler characteristic. It supplies the openness input to the treatment of the relative Picard functor and its algebraic-equivalence cut, being used by the statements on opens cutting out the algebraic-equivalence locus for glued smooth curve degenerations and line degenerations, and by the local finite presentation and surjectivity statements for the corresponding subpresheaf.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isOpen_setOf_isAlgEquivZero_fibre_of_twoStrata.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.isOpen_setOf_isAlgEquivZero_fibre_of_twoStrata
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (Z₀ : Set ↥(Spec (CommRingCat.of R))) (hZ₀ : IsClosed Z₀)
    (hcut : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t) (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
      IsAlgEquivZero (fibreAt c t s) (fibreModule c t s L.L) →
        ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
          (Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s L.L)).H0 : ℤ) -
              Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s L.L)).H1 =
            (Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (𝟙_ (pullback c t).Modules))).H0 : ℤ) -
              Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (𝟙_ (pullback c t).Modules))).H1)
    (hoff : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t) (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
      t (s (IsLocalRing.closedPoint k)) ∉ Z₀ →
      ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
        (Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s L.L)).H0 : ℤ) -
            Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s L.L)).H1 =
          (Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (𝟙_ (pullback c t).Modules))).H0 : ℤ) -
            Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (𝟙_ (pullback c t).Modules))).H1 →
        IsAlgEquivZero (fibreAt c t s) (fibreModule c t s L.L))
    (hZ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), ∃ U : Set T, IsOpen U ∧
        U ∩ (⇑t) ⁻¹' Z₀ = {x : T | t x ∈ Z₀ ∧ ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
          Set.range ⇑s ⊆ {x} → IsAlgEquivZero (fibreAt c t s) (fibreModule c t s L.L)}) :
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t),
      IsOpen {x : T | ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
        Set.range ⇑s ⊆ {x} → IsAlgEquivZero (fibreAt c t s) (fibreModule c t s L.L)} := by sorry
