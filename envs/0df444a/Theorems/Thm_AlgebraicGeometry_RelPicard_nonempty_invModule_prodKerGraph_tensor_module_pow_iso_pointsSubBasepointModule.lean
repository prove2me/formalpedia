-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule
-- name    : AlgebraicGeometry.RelPicard.nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/68873b87-e5ae-5aff-9505-9e491891d746
-- title:
--   Divisor of r points minus rε splits as a tensor product
-- statement:
--   Let $k$ be a field and let $a\colon A\to\operatorname{Spec} k$ be a separated morphism of schemes that is smooth of relative dimension one. Let $\varepsilon$ be a section of $a$ over the identity of $\operatorname{Spec} k$, that is, a pair consisting of a morphism $\varepsilon_1\colon \operatorname{Spec} k\to A$ together with a proof that $\varepsilon_1$ followed by $a$ is the identity. Let $r$ be a natural number and let $P\colon \mathrm{Fin}\,r\to (\operatorname{Spec} k\to A)$ be a family of morphisms with $P_i$ followed by $a$ equal to the identity for every $i$. All modules below live on the pullback of $a$ along the identity of $\operatorname{Spec} k$. The assertion is that the following two modules are isomorphic (the statement is the nonemptiness of the type of isomorphisms): on one side, the tensor product of `invModule` of `prodKerGraph a P hP`, the product over $i$ of the kernel ideal sheaf data of the graph morphism of $P_i$, with `module` of the $r$-th power of the ideal sheaf data `I` of the degree-one relative effective Cartier divisor `RelEffCartierDiv.ofPoint` attached to $\varepsilon$ (namely the kernel ideal of the graph of $\varepsilon$); here for an ideal sheaf datum $I$, `module` is the kernel of the canonical map from the unit module to the pushforward of the unit along the closed immersion of the associated subscheme, and `invModule` is its dual. On the other side stands `pointsSubBasepointModule` evaluated at $\varepsilon$ and the list of the sections $\langle P_i, hP_i\rangle$ obtained from the family $P$: the right-nested tensor product, over the entries $t$ of the list, of the modules `lineBundle` of the divisor `RelEffCartierDiv.ofPoint` of $t$ tensored with `idealModule` of the divisor `RelEffCartierDiv.ofPoint` of $\varepsilon$, with the tensor unit for the empty list.
--
--   This is the divisor-theoretic identity $\mathcal O(P_0+\dots+P_{r-1})\otimes\mathcal O(-r\varepsilon)\cong\bigotimes_i\bigl(\mathcal O(P_i)\otimes\mathcal O(-\varepsilon)\bigr)$ on a smooth separated curve over a field, in the form needed to compare the line bundle of a sum of rational points with the iterated tensor product of the individual differences from the base point $\varepsilon$. It is used in the Abel–Jacobi description of degree-zero line bundles, being cited by [`AlgebraicGeometry.RelPicard.IsAlgEquivZero.exists_iso_pointsSubBasepointModule`](thm.html#AlgebraicGeometry.RelPicard.IsAlgEquivZero.exists_iso_pointsSubBasepointModule) and by [`AlgebraicGeometry.RelPicard.isAlgEquivZero_iff_eulerChar_sectionsOf_eq`](thm.html#AlgebraicGeometry.RelPicard.isAlgEquivZero_iff_eulerChar_sectionsOf_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule
    {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    [IsSeparated a] [SmoothOfRelativeDimension 1 a]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) {r : ℕ}
    (P : Fin r → (Spec (CommRingCat.of k) ⟶ A)) (hP : ∀ i, P i ≫ a = 𝟙 _) :
    Nonempty ((prodKerGraph a P hP).invModule ⊗ ((RelEffCartierDiv.ofPoint a ε.1 ε.2).I ^ r).module ≅
      pointsSubBasepointModule (a := a) ε
        (List.ofFn fun i => (⟨P i, hP i⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a))) := by sorry
