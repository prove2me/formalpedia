-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_IsFibreReading_appLE_of_comp_eq
-- name    : AlgebraicGeometry.SmallExtension.IsFibreReading.appLE_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/1ef02276-17cc-5340-9e49-ecb6cd3746a1
-- title:
--   Fibre readings transport along a morphism of thickenings
-- statement:
--   Fix a commutative ring $B_1$ and a field $k$, a $k$-vector space $V$ that is also a $B_1$-module, and a $B_1$-linear map $\iota : V \to B_1$. Let $f : X \to \operatorname{Spec} B_1$ and $f' : X' \to \operatorname{Spec} B_1$, let $f_k : X_k \to \operatorname{Spec} k$ and $f_k' : X_k' \to \operatorname{Spec} k$, and let $i : X_k \to X$, $i' : X_k' \to X'$ be arbitrary morphisms of schemes. Let $h : X' \to X$ with $h$ followed by $f$ equal to $f'$, and $h_k : X_k' \to X_k$ with $h_k$ followed by $i$ equal to $i'$ followed by $h$, and $h_k$ followed by $f_k$ equal to $f_k'$. Let $U \subseteq X$, $W \subseteq X_k$ with $W \le i^{-1}U$, $U' \subseteq X'$ with $U' \le h^{-1}U$, and $W' \subseteq X_k'$ with $W' \le i'^{-1}U'$ and $W' \le h_k^{-1}W$ be open. Let $\delta \in \Gamma(X,U)$, and let $w : V^\vee \to \Gamma(X_k,W)$, $w' : V^\vee \to \Gamma(X_k',W')$ be $k$-linear, where $V^\vee = \operatorname{Hom}_k(V,k)$ and the target rings carry the $k$-algebra structures induced by $f_k$ and $f_k'$ via `algebraOfHom`, and assume $w'(\xi)$ is the image of $w(\xi)$ under $h_k^\sharp : \Gamma(X_k,W) \to \Gamma(X_k',W')$ for all $\xi$. Assume `IsFibreReading` holds for $(f,f_k,i,U,W,\delta,w)$, that is: there are $n \in \mathbb{N}$, $v : \operatorname{Fin} n \to V$ and $s : \operatorname{Fin} n \to \Gamma(X,U)$ with $\sum_j \operatorname{alg}_{B_1}(\iota(v_j))\, s_j = \delta$ in $\Gamma(X,U)$ (the $B_1$-algebra structure coming from $f$) and, for every $\xi \in V^\vee$, $w(\xi) = \sum_j \xi(v_j) \cdot \bigl(i^\sharp(s_j)\bigr)|_W$. The conclusion is that `IsFibreReading` holds for $(f',f_k',i',U',W', h^\sharp(\delta)|_{U'}, w')$, where $h^\sharp(\delta)|_{U'}$ denotes the image of $\delta$ under $h$'s comparison map $\Gamma(X,U) \to \Gamma(X',U')$.
--
--   This is the functoriality of the fibre-reading relation: a section of $\mathcal{O}_X$ on $U$ presented by a $V$-linear combination, together with the induced $k$-linear reading of its restriction to the fibre, pulls back along a morphism of schemes over $\operatorname{Spec} B_1$ compatible with the chosen fibre maps. It is used in the construction of Picard deformation and obstruction cocycles for a small extension, where readings must be compared after passing to a refining cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_IsFibreReading_appLE_of_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.SmallExtension Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.SmallExtension.IsFibreReading.appLE_of_comp_eq
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    {X X' Xk Xk' : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of B₁)) (f' : X' ⟶ Spec (CommRingCat.of B₁))
    (fk : Xk ⟶ Spec (CommRingCat.of k)) (fk' : Xk' ⟶ Spec (CommRingCat.of k))
    (i : Xk ⟶ X) (i' : Xk' ⟶ X')
    (h : X' ⟶ X) (hh : h ≫ f = f')
    (hk : Xk' ⟶ Xk) (hhk : hk ≫ i = i' ≫ h) (hfk : hk ≫ fk = fk')
    (U : X.Opens) (W : Xk.Opens) (hW : W ≤ i ⁻¹ᵁ U)
    (U' : X'.Opens) (hU' : U' ≤ h ⁻¹ᵁ U) (W' : Xk'.Opens) (hW' : W' ≤ i' ⁻¹ᵁ U') (hWk : W' ≤ hk ⁻¹ᵁ W)
    (δ : Γ(X, U)) (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).obj W)
    (w' : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk').obj W')
    (hw' : ∀ ξ : Module.Dual k V, w' ξ = (hk.appLE W W' hWk).hom (w ξ))
    (hw : IsFibreReading V ι f fk i U W hW δ w) :
    IsFibreReading V ι f' fk' i' U' W' hW' ((h.appLE U U' hU').hom δ) w' := by sorry
