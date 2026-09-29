-- Prove2me | Theorems.Thm_AlgebraicGeometry_prodKerGraph_comap_fst_eq_prodKerGraph_comap_of_isPullback
-- name    : AlgebraicGeometry.prodKerGraph_comap_fst_eq_prodKerGraph_comap_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/b9a35470-9d11-585c-af3c-ba4fb640b9fa
-- title:
--   Product of graph kernels under cartesian base change
-- statement:
--   Let $f : \mathcal C \to S$ and $f' : \mathcal C' \to S'$ be separated morphisms of schemes, and let $h : S' \to S$, $g' : \mathcal C' \to \mathcal C$ be morphisms making the square with $g', f', f, h$ cartesian (`IsPullback g' f' f h`), so that $\mathcal C'$ is a fibre product $\mathcal C \times_S S'$. Fix $r \in \mathbb N$ and families $a : \mathrm{Fin}\,r \to (S \to \mathcal C)$ with $a_i \circ f = \mathrm{id}_S$ and $b : \mathrm{Fin}\,r \to (S' \to \mathcal C')$ with $b_i \circ f' = \mathrm{id}_{S'}$, i.e. sections of $f$ and of $f'$, such that $g' \circ b_i = a_i \circ h$ for all $i$. Finally let $\theta$ be a morphism from the pullback of $\mathrm{pr}_2 : \mathcal C \times_S S \to S$ along $h$ to $\mathcal C' \times_{S'} S'$ satisfying $g' \circ \mathrm{pr}_1 \circ \theta = \mathrm{pr}_1 \circ \mathrm{pr}_1$ and $\mathrm{pr}_2 \circ \theta = \mathrm{pr}_2$. Write $\mathrm{prodKerGraph}$ for the product over $i$ of the kernel ideal sheaves of the graph sections $\mathrm{graphOver}$, the latter being the lift of $(a_i, \mathrm{id}_S)$ into $\mathcal C \times_S S$, respectively of $(b_i, \mathrm{id}_{S'})$ into $\mathcal C' \times_{S'} S'$. The conclusion is that the two ideal sheaves on $(\mathcal C \times_S S) \times_S S'$ obtained by pulling back $\mathrm{prodKerGraph}\,f\,a$ along the first projection and $\mathrm{prodKerGraph}\,f'\,b$ along $\theta$ coincide.
--
--   This is the base-change compatibility of the divisor-like ideal sheaf attached to a finite family of sections, in the case where the curve itself moves along a cartesian square; its companion [`AlgebraicGeometry.prodKerGraph_comap_mapOnProdOver`](thm.html#AlgebraicGeometry.prodKerGraph_comap_mapOnProdOver) moves only the test scheme over a fixed curve. It is used in the treatment of Drinfeld bases for Weierstrass models under base change, via [`WeierstrassCurve.DrinfeldGlobal.basisDivisor_comap_fst_eq_basisDivisor_comap_theta`](thm.html#WeierstrassCurve.DrinfeldGlobal.basisDivisor_comap_fst_eq_basisDivisor_comap_theta).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_prodKerGraph_comap_fst_eq_prodKerGraph_comap_of_isPullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.prodKerGraph_comap_fst_eq_prodKerGraph_comap_of_isPullback
    {𝒞 𝒞' S S' : Scheme.{u}} (f : 𝒞 ⟶ S) (f' : 𝒞' ⟶ S') [IsSeparated f] [IsSeparated f']
    (h : S' ⟶ S) (g' : 𝒞' ⟶ 𝒞) (H : IsPullback g' f' f h)
    {r : ℕ} (a : Fin r → (S ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = 𝟙 S)
    (b : Fin r → (S' ⟶ 𝒞')) (hb : ∀ i, b i ≫ f' = 𝟙 S')
    (hab : ∀ i, b i ≫ g' = h ≫ a i)
    (θ : pullback (pullback.snd f (𝟙 S)) h ⟶ pullback f' (𝟙 S'))
    (hθ₁ : θ ≫ pullback.fst f' (𝟙 S') ≫ g' = pullback.fst (pullback.snd f (𝟙 S)) h ≫ pullback.fst f (𝟙 S))
    (hθ₂ : θ ≫ pullback.snd f' (𝟙 S') = pullback.snd (pullback.snd f (𝟙 S)) h) :
    (prodKerGraph f a ha).comap (pullback.fst (pullback.snd f (𝟙 S)) h) =
      (prodKerGraph f' b hb).comap θ := by sorry
