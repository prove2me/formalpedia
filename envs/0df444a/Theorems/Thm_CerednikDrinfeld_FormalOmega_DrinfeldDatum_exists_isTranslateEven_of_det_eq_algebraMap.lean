-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isTranslateEven_of_det_eq_algebraMap
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isTranslateEven_of_det_eq_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/ceab7e0f-3223-5550-98dc-231858617c0f
-- title:
--   Existence of the even translate when det(cg⁻¹) is a unit
-- statement:
--   Let $\mathcal O$ be a commutative ring, $K$ a field equipped with an $\mathcal O$-algebra structure, $\pi \in \mathcal O$, and $B$ a commutative $\mathcal O$-algebra. Let $Q$ be a Drinfeld datum `DrinfeldDatum π B`, that is: two families $x \mapsto N_0(x)$, $x \mapsto N_1(x)$ of $\mathcal O$-submodules of $K^2$ indexed by $x \in \operatorname{Spec} B$, each a full lattice (finitely generated with $K$-span all of $K^2$), with $N_0(x) \le N_1(x)$ and $\pi N_1(x) \subseteq N_0(x)$, the membership locus $\{x : v \in N_i(x)\}$ being open for every $v \in K^2$; invertible $B$-modules $T_0, T_1$ with $B$-linear maps $\Pi_0 : T_0 \to T_1$ and $\Pi_1 : T_1 \to T_0$ whose two composites are multiplication by $\pi$; and rigidifications $u_i(x)$ from the base change of $N_i(x)$ to the local ring of $B$ at $x$ into the stalk of $T_i$ at $x$, compatible with the inclusion $N_0(x) \le N_1(x)$ via $\Pi_0$ and with multiplication by $\pi$, together with the remaining compatibility conditions of the structure. Let $g \in GL_2(K)$, $c \in K^\times$ and $e \in \mathcal O^\times$, and write $h := (c\cdot 1)\,g^{-1}$, where $c \cdot 1$ is the scalar matrix `scalarGL c`. Assume $\det h$ equals the image of $e$ under $\mathcal O \to K$. Then there exists a Drinfeld datum $Q'$ over $B$ with `Q.IsTranslateEven g c Q'`, i.e. the type `TranslateEven h`-data is nonempty: $N_i'(x)$ is the transport of $N_i(x)$ along $h$ for both $i$ and all $x$, and there are $B$-linear isomorphisms $\tau_i : T_i \xrightarrow{\sim} T_i'$ commuting with $\Pi_0$ and $\Pi_1$ and carrying $u_i(x)(1 \otimes v)$ to $u_i'(x)(1 \otimes h v)$ for $v \in N_i(x)$.
--
--   This is the even case of the translation (pull-back) construction for Drinfeld data along an element of $GL_2(K)$ renormalised by a scalar, as in the Čerednik–Drinfeld uniformisation theory: when $\det(c g^{-1})$ lies in the image of $\mathcal O^\times$ the translated lattices again carry a datum of the same parity. It is invoked by [`CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isTranslateEven_or_exists_isTranslateOdd`](thm.html#CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isTranslateEven_or_exists_isTranslateOdd), which splits the general case according to the parity of the valuation of the determinant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isTranslateEven_of_det_eq_algebraMap.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isTranslateEven_of_det_eq_algebraMap
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (Q : DrinfeldDatum (K := K) π B) (g : Matrix.GeneralLinearGroup (Fin 2) K) (c : Kˣ) (e : 𝒪ˣ)
    (hdet : ((Matrix.GeneralLinearGroup.det (scalarGL c * g⁻¹) : Kˣ) : K) = algebraMap 𝒪 K e) :
    ∃ Q' : DrinfeldDatum (K := K) π B, Q.IsTranslateEven g c Q' := by sorry
