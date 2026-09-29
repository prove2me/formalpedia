-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isTranslateEven_or_exists_isTranslateOdd
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isTranslateEven_or_exists_isTranslateOdd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/f070e460-5e35-5b06-887c-ee3653ed94fb
-- title:
--   Existence of even or odd GL₂(K)-translates of a Drinfeld datum
-- statement:
--   Let $\mathcal O$ be a discrete valuation domain, let $K$ be a field carrying an $\mathcal O$-algebra structure that makes it the fraction field of $\mathcal O$, let $\pi \in \mathcal O$ be irreducible, and let $B$ be a commutative $\mathcal O$-algebra. Let $Q$ be a Drinfeld datum over $B$ with parameter $\pi$, that is: two families $N_0(x) \le N_1(x)$ of finitely generated $\mathcal O$-submodules of $K^2$ spanning $K^2$ over $K$, indexed by $x \in \operatorname{Spec} B$, with $\pi N_1(x) \subseteq N_0(x)$ and with $\{x : v \in N_i(x)\}$ open for each $v \in K^2$; two invertible $B$-modules $T_0, T_1$ together with $B$-linear maps $\Pi_0 : T_0 \to T_1$, $\Pi_1 : T_1 \to T_0$ whose two composites are multiplication by $\pi$; and for each $x$ maps $u_i(x)$ from the base change of $N_i(x)$ to the local ring at $x$ into the stalk of $T_i$ at $x$, compatible with the inclusions $N_0 \subseteq N_1$ and with multiplication by $\pi$ via $\Pi_0, \Pi_1$, subject to the remaining axioms of the structure. Let $g \in \mathrm{GL}_2(K)$. The assertion is a disjunction. Either there are $c \in K^\times$ and a Drinfeld datum $Q'$ over $B$ admitting an even translate datum: $Q'.N_i(x)$ is the image of $N_i(x)$ under the matrix $c \cdot g^{-1}$ for all $x$ and $i = 0,1$, together with $B$-linear isomorphisms $\tau_i : T_i \cong Q'.T_i$ interchanging $\Pi_0, \Pi_1$ with $Q'.\Pi_0, Q'.\Pi_1$ and matching $u_i$ with $Q'.u_i$ under translation of lattice vectors by $c \cdot g^{-1}$; or there are $c_0, c_1 \in K^\times$ with $c_0 = \pi c_1$ and a Drinfeld datum $Q'$ admitting an odd translate datum: $Q'.N_0(x)$ is the image of $N_1(x)$ under $c_0 \cdot g^{-1}$, $Q'.N_1(x)$ is the image of $N_0(x)$ under $c_1 \cdot g^{-1}$, together with $B$-linear isomorphisms $\sigma_0 : T_1 \cong Q'.T_0$ and $\sigma_1 : T_0 \cong Q'.T_1$ exchanging the roles of $\Pi_0$ and $\Pi_1$ and matching $u_1$ with $Q'.u_0$ and $u_0$ with $Q'.u_1$ accordingly.
--
--   This is the existence half of Drinfeld's action of $\mathrm{GL}_2(K)$ on the functor of quadruples underlying the $p$-adic uniformisation of Shimura curves: every $g$ admits a translate of a given datum, in the even or the odd normalisation according to the parity of the valuation of $\det g$. It is used in the analysis of base change of quadruples, where a cover of the base is produced on which the translating scalars and the translate data are realised.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isTranslateEven_or_exists_isTranslateOdd.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isTranslateEven_or_exists_isTranslateOdd
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (Q : DrinfeldDatum (K := K) π B) (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    (∃ (c : Kˣ) (Q' : DrinfeldDatum (K := K) π B), Q.IsTranslateEven g c Q') ∨
    (∃ (c₀ c₁ : Kˣ) (Q' : DrinfeldDatum (K := K) π B), Q.IsTranslateOdd g c₀ c₁ Q') := by sorry
