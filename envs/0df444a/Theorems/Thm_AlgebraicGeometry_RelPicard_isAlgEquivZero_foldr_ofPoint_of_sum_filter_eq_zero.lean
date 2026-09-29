-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_foldr_ofPoint_of_sum_filter_eq_zero
-- name    : AlgebraicGeometry.RelPicard.isAlgEquivZero_foldr_ofPoint_of_sum_filter_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/7d384da4-5270-58b1-8008-070d98c4ee6f
-- title:
--   Degree-zero point twists are algebraically equivalent to zero
-- statement:
--   Let $k$ be an algebraically closed field and let $c \colon C \to \operatorname{Spec} k$ be a morphism of schemes that is proper, smooth of relative dimension one and geometrically integral. Let $z \colon \mathrm{Fin}\,m \to (\operatorname{Spec} k \to C)$ be a finite family of morphisms with $z_i$ followed by $c$ equal to the identity for every $i$, i.e. a family of $k$-points of $C$; let $\mathrm{keep}$ be a decidable predicate on $\mathrm{Fin}\,m$ and let $a, b \colon \mathrm{Fin}\,m \to \mathbb{N}$ be multiplicities subject to the single numerical hypothesis $\sum_{i \in \mathrm{keep}} (a_i - b_i) = 0$ in $\mathbb{Z}$, the sum being over the kept indices. For each $i$ write $I_i$ for the ideal sheaf datum on $\mathrm{pullback}\, c\, (\mathbb{1}_{\operatorname{Spec} k})$ underlying the relative effective Cartier divisor `RelEffCartierDiv.ofPoint` attached to $z_i$, namely the kernel ideal of the graph of $z_i$, whose associated module $I^{\,\cdot}$`.module` is the kernel of the map from the unit module to the pushforward of the unit along the closed subscheme inclusion, and whose $I^{\,\cdot}$`.invModule` is its monoidal dual. Consider the module $L$ on $\mathrm{pullback}\, c\, (\mathbb{1}_{\operatorname{Spec} k})$ obtained by folding the list $\mathrm{finRange}\,m$ from the right, starting at the tensor unit, inserting for each kept index $i$ the factor $(I_i^{a_i})^{\vee} \otimes I_i^{b_i}$ and skipping the discarded indices. The conclusion is `IsAlgEquivZero` for $L$ relative to the structure morphism $\mathrm{pullback.snd}\, c\, (\mathbb{1}_{\operatorname{Spec} k})$: there are a scheme $T'$, a morphism $h \colon T' \to \operatorname{Spec} k$ that is locally of finite type and geometrically integral, an invertible module $M$ on the fibre product of $\mathrm{pullback}\, c\, (\mathbb{1})$ with $T'$ over $\operatorname{Spec} k$, and two sections $t_0, t_1$ of $h$ (morphisms $\operatorname{Spec} k \to T'$ splitting $h$), such that the base change of $M$ along $t_0$ is isomorphic to the unit module and its base change along $t_1$ is isomorphic to the pullback of $L$ along the first projection.
--
--   This is the statement that a divisor class of total degree zero supported on $k$-points of a smooth proper geometrically integral curve lies in the identity component of the Picard group, in the form of algebraic equivalence to zero via an invertible module over a geometrically integral parameter scheme. It feeds the construction of morphisms into the relative Picard functor, in particular the representability statements producing sections of the Poincaré bundle over such point twists and the statements about glued smooth curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_foldr_ofPoint_of_sum_filter_eq_zero.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.isAlgEquivZero_foldr_ofPoint_of_sum_filter_eq_zero
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    {m : ℕ} (z : Fin m → (Spec (CommRingCat.of k) ⟶ C)) (hz : ∀ i, z i ≫ c = 𝟙 _)
    (keep : Fin m → Prop) [DecidablePred keep] (a b : Fin m → ℕ)
    (hdeg : (∑ i ∈ Finset.univ.filter keep, ((a i : ℤ) - (b i : ℤ))) = 0) :
    IsAlgEquivZero (pullback.snd c (𝟙 (Spec (CommRingCat.of k))))
      ((List.finRange m).foldr
        (fun i M => if keep i then
          ((RelEffCartierDiv.ofPoint c (z i) (hz i)).I ^ (a i)).invModule ⊗
            ((RelEffCartierDiv.ofPoint c (z i) (hz i)).I ^ (b i)).module ⊗ M
          else M)
        (𝟙_ (pullback c (𝟙 (Spec (CommRingCat.of k)))).Modules)) := by sorry
