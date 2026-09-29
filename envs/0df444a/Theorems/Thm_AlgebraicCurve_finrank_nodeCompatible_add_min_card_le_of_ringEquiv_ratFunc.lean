-- Prove2me | Theorems.Thm_AlgebraicCurve_finrank_nodeCompatible_add_min_card_le_of_ringEquiv_ratFunc
-- name    : AlgebraicCurve.finrank_nodeCompatible_add_min_card_le_of_ringEquiv_ratFunc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/7f274ab3-1479-50b0-80d6-d970a3897ad5
-- title:
--   Glued sections on two rational curves: a dimension bound
-- statement:
--   Let $k$ be an algebraically closed field and $F$ a field extension of $k$ equipped with a ring isomorphism $e : k(X) \to F$ that is the identity on $k$, i.e. $e(\mathrm{alg\,map}(c)) = \mathrm{alg\,map}(c)$ for all $c \in k$; write $\Phi =$ `Place.congrEquiv e he` for the induced bijection between the places of $k(X)/k$ and of $F/k$ (a place being a valuation subring of the field, containing the image of $k$, distinct from the whole field and a principal ideal ring; $\Phi$ pulls back valuation subrings along $e^{-1}$). Let $\iota$ be a finite index type, let $E_1, E_2$ be divisors of $F/k$ (finitely supported $\mathbb Z$-valued functions on places) with $E_1, E_2 \ge 0$, and let $a, b : \iota \to k$ be injective families with $E_1(\Phi(P_{a_i})) = 0$ and $E_2(\Phi(P_{b_i})) = 0$ for all $i$, where $P_c$ denotes the place of $k(X)$ attached to the irreducible polynomial $X - c$. Let $T$ be a $k$-submodule of $F \times F$ whose members are exactly the pairs $p$ with $p_1$ in the Riemann–Roch space of $E_1$ (i.e. $v(p_1) \le \exp(E_1(v))$ for every place $v$), $p_2$ in that of $E_2$, and such that for each $i$ there is $c \in k$ with $p_1$ having value $c$ at $\Phi(P_{a_i})$ and $p_2$ having value $c$ at $\Phi(P_{b_i})$ (having value $c$ at a place means lying in its valuation subring with residue the image of $c$ in the residue field). Then, in $\mathbb Z$, $$\dim_k T + \min\bigl(\#\iota,\ \max(\deg E_1, \deg E_2) + 1\bigr) \le (\deg E_1 + 1) + (\deg E_2 + 1),$$ the degree of a divisor being $\sum_v D(v)\,\deg(v)$.
--
--   The bound counts sections of line bundles on two copies of $\mathbb P^1_k$ glued transversally at the pairs of points $a_i \sim b_i$: $T$ is the kernel of the difference of the two evaluation maps $L(E_1) \times L(E_2) \to k^{\iota}$, whose rank is at least $\min(\#\iota, \max(\deg E_1, \deg E_2) + 1)$, while $\dim_k L(E_j) = \deg E_j + 1$ on a rational function field. It is used in the construction of sections of prescribed residues on level-one prolongation pairs of places of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_finrank_nodeCompatible_add_min_card_le_of_ringEquiv_ratFunc.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.finrank_nodeCompatible_add_min_card_le_of_ringEquiv_ratFunc
    {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
    (e : RatFunc k ≃+* F) (he : ∀ c : k, e (algebraMap k (RatFunc k) c) = algebraMap k F c)
    {ι : Type*} [Fintype ι]
    (E₁ E₂ : Divisor k F) (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (a b : ι → k) (ha : Function.Injective a) (hb : Function.Injective b)
    (haE : ∀ i, E₁ (Place.congrEquiv e he (RationalFunctionField.placeOfPoint k (a i))) = 0)
    (hbE : ∀ i, E₂ (Place.congrEquiv e he (RationalFunctionField.placeOfPoint k (b i))) = 0)
    (T : Submodule k (F × F))
    (hT : ∀ p, p ∈ T ↔ p.1 ∈ riemannRochSpace E₁ ∧ p.2 ∈ riemannRochSpace E₂ ∧
      ∀ i, ∃ c : k, (Place.congrEquiv e he (RationalFunctionField.placeOfPoint k (a i))).HasValue p.1 c ∧
        (Place.congrEquiv e he (RationalFunctionField.placeOfPoint k (b i))).HasValue p.2 c) :
    (Module.finrank k T : ℤ) + min (Fintype.card ι : ℤ) (max E₁.degree E₂.degree + 1)
      ≤ (E₁.degree + 1) + (E₂.degree + 1) := by sorry
