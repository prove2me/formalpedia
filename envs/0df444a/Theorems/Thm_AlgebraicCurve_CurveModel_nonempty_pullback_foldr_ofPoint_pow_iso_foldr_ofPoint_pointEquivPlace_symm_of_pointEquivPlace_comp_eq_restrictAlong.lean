-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_nonempty_pullback_foldr_ofPoint_pow_iso_foldr_ofPoint_pointEquivPlace_symm_of_pointEquivPlace_comp_eq_restrictAlong
-- name    : AlgebraicCurve.CurveModel.nonempty_pullback_foldr_ofPoint_pow_iso_foldr_ofPoint_pointEquivPlace_symm_of_pointEquivPlace_comp_eq_restrictAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/71f29436-3495-5b10-87c8-d5fbec690150
-- title:
--   Pull-back of a point twist is the conorm twist
-- statement:
--   Let $k$ be an algebraically closed field and let $F$, $F'$ be fields with $k$-algebra structures for which every nonzero element admits a divisor recording its orders at all places and of degree $0$ (`HasPrincipalDivisors`). Let $M$, $M'$ be curve models over $k$ of $F$ and $F'$ respectively: integral schemes $M.C$, $M'.C$ proper and smooth of relative dimension $1$ over $\operatorname{Spec} k$, together with identifications of $F$, $F'$ with their function fields over $k$ and bijections between closed points and places matching stalks with valuation subrings. Let $\varphi\colon F \to F'$ be a $k$-algebra map whose underlying ring map is integral, and let $g\colon M'.C \to M.C$ satisfy $M'.\mathrm{toBase} = g$ followed by $M.\mathrm{toBase}$, and be compatible with $\varphi$ on points: for every section $x'$ of $M'.\mathrm{toBase}$ over $\operatorname{Spec} k$, the place of $F$ attached by `M.pointEquivPlace` to $x'$ followed by $g$ is the restriction along $\varphi$ of the place of $F'$ attached to $x'$. Let $g_k$ be a morphism $\operatorname{pullback} M'.\mathrm{toBase}\,(\mathbb{1}) \to \operatorname{pullback} M.\mathrm{toBase}\,(\mathbb{1})$ commuting with the first projections via $g$ and with the second projections. Let $x\colon \mathrm{Fin}\,n$ be a family of $k$-sections of $M.\mathrm{toBase}$, let $\mathrm{pos}, \mathrm{neg}\colon \mathrm{Fin}\,n \to \mathbb{N}$, and let $\bar D$ be a divisor of $F'$ (a finitely supported $\mathbb{Z}$-valued function on places) such that for every place $W$ of $F'$, $$\bar D(W) = e(W/\varphi)\sum_i \bigl[\,\text{place of }x_i = W|_\varphi\,\bigr]\,(\mathrm{pos}_i - \mathrm{neg}_i),$$ with $e(W/\varphi)$ the ramification index along $\varphi$. Then the following two modules on $\operatorname{pullback} M'.\mathrm{toBase}\,(\mathbb{1})$ are isomorphic (the type of isomorphisms is nonempty): the pull-back along $g_k$ of the right fold over $\mathrm{Fin}\,n$, starting from the monoidal unit, of $N \mapsto (I_{x_i}^{\mathrm{pos}_i})^{\vee} \otimes I_{x_i}^{\mathrm{neg}_i} \otimes N$, where $I_{x_i}$ is the ideal sheaf of the relative effective Cartier divisor cut out by the graph of $x_i$ and $(\cdot)^{\vee}$ denotes its dual module; and the right fold over the support of $\bar D$, listed, of $N \mapsto (J_W^{\bar D(W)_+})^{\vee} \otimes J_W^{(-\bar D(W))_+} \otimes N$, where $J_W$ is the graph ideal sheaf of the $k$-section of $M'.\mathrm{toBase}$ corresponding to $W$ under `M'.pointEquivPlace` and $(\cdot)_+$ denotes the truncation of an integer to $\mathbb{N}$.
--
--   This is the compatibility of the ideal-sheaf (point-twist) construction with pull-back of divisors along a finite map of smooth proper curves: the pull-back along $g_k$ of a twist by $\sum_i (\mathrm{pos}_i - \mathrm{neg}_i)[x_i]$ is the twist by the conorm divisor $\bar D = \varphi^{*}\bigl(\sum_i (\mathrm{pos}_i - \mathrm{neg}_i)[x_i]\bigr)$, expressed in the fold form in which such twists are built. It is used in the computation of classes in the degree-zero Picard group attached to points of a model of $X_1(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_nonempty_pullback_foldr_ofPoint_pow_iso_foldr_ofPoint_pointEquivPlace_symm_of_pointEquivPlace_comp_eq_restrictAlong.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open Classical

theorem AlgebraicCurve.CurveModel.nonempty_pullback_foldr_ofPoint_pow_iso_foldr_ofPoint_pointEquivPlace_symm_of_pointEquivPlace_comp_eq_restrictAlong
    {k : Type u} [Field k] [IsAlgClosed k]
    {F : Type v} [Field F] [Algebra k F] [HasPrincipalDivisors k F] {F' : Type v} [Field F'] [Algebra k F'] [HasPrincipalDivisors k F']
    (M : CurveModel k F) (M' : CurveModel k F')
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral)
    (g : M'.C ⟶ M.C) (hg : g ≫ M.toBase = M'.toBase)
    (hgφ : ∀ x' : {q : Spec (CommRingCat.of k) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _},
      M.pointEquivPlace ⟨x'.1 ≫ g, by rw [Category.assoc, hg]; exact x'.2⟩ = (M'.pointEquivPlace x').restrictAlong φ hφ)
    (gk : pullback M'.toBase (𝟙 (Spec (CommRingCat.of k))) ⟶ pullback M.toBase (𝟙 (Spec (CommRingCat.of k))))
    (hgk₁ : gk ≫ pullback.fst _ _ = pullback.fst _ _ ≫ g) (hgk₂ : gk ≫ pullback.snd _ _ = pullback.snd _ _)
    {n : ℕ} (x : Fin n → {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) (pos neg : Fin n → ℕ)
    (Dbar : Divisor k F')
    (hDbar : ∀ W : Place k F', Dbar W = (Place.ramificationIndexAlong φ W : ℤ) *
      ∑ i, (if M.pointEquivPlace (x i) = W.restrictAlong φ hφ then ((pos i : ℤ) - (neg i : ℤ)) else 0)) :
    Nonempty ((Scheme.Modules.pullback gk).obj
        ((List.finRange n).foldr (fun i N =>
            ((RelEffCartierDiv.ofPoint M.toBase (x i).1 (x i).2).I ^ pos i).invModule ⊗
              ((RelEffCartierDiv.ofPoint M.toBase (x i).1 (x i).2).I ^ neg i).module ⊗ N)
          (𝟙_ (pullback M.toBase (𝟙 (Spec (CommRingCat.of k)))).Modules)) ≅
      (Dbar.support.toList).foldr (fun W N =>
          ((RelEffCartierDiv.ofPoint M'.toBase (M'.pointEquivPlace.symm W).1 (M'.pointEquivPlace.symm W).2).I ^ (Dbar W).toNat).invModule ⊗
            ((RelEffCartierDiv.ofPoint M'.toBase (M'.pointEquivPlace.symm W).1 (M'.pointEquivPlace.symm W).2).I ^ (-(Dbar W)).toNat).module ⊗ N)
        (𝟙_ (pullback M'.toBase (𝟙 (Spec (CommRingCat.of k)))).Modules)) := by sorry
