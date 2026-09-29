-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isTranslateOdd_of_det_mul_eq_algebraMap
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isTranslateOdd_of_det_mul_eq_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/80ec4c6e-00c9-54fa-bafc-f76e68c1d218
-- title:
--   Existence of the odd translate of a Drinfeld datum
-- statement:
--   Let $\mathcal O$ be a commutative ring, $K$ a field equipped with an $\mathcal O$-algebra structure, $\pi \in \mathcal O$, and $B$ a commutative $\mathcal O$-algebra. Let $Q$ be a Drinfeld datum for $\pi$ over $B$, that is: two families $N_0, N_1$ of full $\mathcal O$-lattices in $K^2$ (finitely generated submodules spanning $K^2$ over $K$) indexed by $\operatorname{Spec} B$, with $N_0(x) \le N_1(x)$ and $\pi N_1(x) \subseteq N_0(x)$ for every $x$, such that for each $v \in K^2$ the loci $\{x : v \in N_i(x)\}$ are open; together with invertible $B$-modules $T_0, T_1$, $B$-linear maps $\Pi_0 : T_0 \to T_1$ and $\Pi_1 : T_1 \to T_0$ whose two composites are multiplication by the image of $\pi$ in $B$; and, at each prime $x$, trivialisations $u_0, u_1$ of the base changes of $N_0(x), N_1(x)$ to the local ring at $x$ with values in the stalks of $T_0, T_1$, compatible with the inclusion $N_0(x) \subseteq N_1(x)$ and $\Pi_0$, with multiplication by $\pi$ and $\Pi_1$, and with the remaining conditions of the structure. Let $g \in \mathrm{GL}_2(K)$, let $c_0, c_1 \in K^\times$ and $e \in \mathcal O^\times$, and assume $c_0 = \pi c_1$ in $K$ and $\pi \cdot \det(c_1 g^{-1}) = e$ in $K$, where $c$ denotes the scalar matrix $c \cdot 1$. Then there is a Drinfeld datum $Q'$ for $\pi$ over $B$ which is an odd translate of $Q$ along $g$ renormalised by $(c_0, c_1)$: there exists a structure recording $c_0 = \pi c_1$, the lattice identities $N'_0(x) = (c_0 g^{-1}) N_1(x)$ and $N'_1(x) = (c_1 g^{-1}) N_0(x)$ for all $x$, $B$-linear isomorphisms $\sigma_0 : T_1 \xrightarrow{\sim} T'_0$ and $\sigma_1 : T_0 \xrightarrow{\sim} T'_1$ with $\sigma_1 \circ \Pi_1 = \Pi'_0 \circ \sigma_0$ and $\sigma_0 \circ \Pi_0 = \Pi'_1 \circ \sigma_1$, and the compatibilities $u'_0(1 \otimes (c_0 g^{-1}) w) = \sigma_0 (u_1(1 \otimes w))$ for $w \in N_1(x)$ and $u'_1(1 \otimes (c_1 g^{-1}) v) = \sigma_1 (u_0(1 \otimes v))$ for $v \in N_0(x)$, on stalks at each prime $x$.
--
--   This is the odd, grading-swapping case of the existence of translates of a Drinfeld datum under the action of $\mathrm{GL}_2(K)$, in the form used in the Čerednik–Drinfeld description of the formal upper half plane. It is one of the two cases combined in [`CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isTranslateEven_or_exists_isTranslateOdd`](thm.html#CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isTranslateEven_or_exists_isTranslateOdd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isTranslateOdd_of_det_mul_eq_algebraMap.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isTranslateOdd_of_det_mul_eq_algebraMap
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (Q : DrinfeldDatum (K := K) π B) (g : Matrix.GeneralLinearGroup (Fin 2) K) (c₀ c₁ : Kˣ) (e : 𝒪ˣ)
    (hc : (c₀ : K) = algebraMap 𝒪 K π * c₁)
    (hdet : algebraMap 𝒪 K π * ((Matrix.GeneralLinearGroup.det (scalarGL c₁ * g⁻¹) : Kˣ) : K) = algebraMap 𝒪 K e) :
    ∃ Q' : DrinfeldDatum (K := K) π B, Q.IsTranslateOdd g c₀ c₁ Q' := by sorry
