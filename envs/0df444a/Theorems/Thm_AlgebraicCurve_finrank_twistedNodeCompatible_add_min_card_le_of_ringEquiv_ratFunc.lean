-- Prove2me | Theorems.Thm_AlgebraicCurve_finrank_twistedNodeCompatible_add_min_card_le_of_ringEquiv_ratFunc
-- name    : AlgebraicCurve.finrank_twistedNodeCompatible_add_min_card_le_of_ringEquiv_ratFunc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/6df81a15-9cc5-5cc8-9d2e-0e294d0204b5
-- title:
--   Dimension bound for twisted node-compatible pairs of sections
-- statement:
--   Let $k$ be an algebraically closed field, $F$ a field and a $k$-algebra, and let $e : k(X) \to F$ be a ring isomorphism that is $k$-linear in the sense that $e(\mathrm{algebraMap}\,c) = \mathrm{algebraMap}\,c$ for every $c \in k$. Places of $F/k$ are valuation subrings of $F$ containing $k$, proper in $F$ and principal ideal rings; divisors are finitely supported $\mathbb{Z}$-valued functions on places, with $\deg$ the sum of the values weighted by the residue degrees. Let $E_1, E_2$ be divisors with $\deg E_j \ge -1$, let $\iota$ be a finite index type, let $a, b : \iota \to k$ be injective, and let $\lambda_i \in k$ be nonzero. Write $P_c$ for the place of $F/k$ obtained by transporting along `Place.congrEquiv e he` the place of $k(X)$ attached to the irreducible polynomial $X - c$. Let $T$ be a $k$-submodule of $F \times F$ consisting exactly of the pairs $p = (p_1,p_2)$ such that $p_1$ lies in the Riemann–Roch space $\{f : v(f) \le \exp(E_1 v)\ \forall v\}$, $p_2$ lies in that of $E_2$, and for every $i$ there is $c \in k$ with $e(X - a_i)^{E_1(P_{a_i})} p_1$ lying in the valuation ring at $P_{a_i}$ with residue $\lambda_i c$, and $e(X - b_i)^{E_2(P_{b_i})} p_2$ lying in the valuation ring at $P_{b_i}$ with residue $c$. Then $\dim_k T + \min(\#\iota, \max(\deg E_1, \deg E_2) + 1) \le (\deg E_1 + 1) + (\deg E_2 + 1)$ in $\mathbb{Z}$.
--
--   The pairs described are the global sections of a line bundle of bidegree $(\deg E_1, \deg E_2)$ on two projective lines glued at the nodes $a_i \sim b_i$ with gluing parameters $\lambda_i$, the divisors $E_j$ recording the branch orders of a local generator; the inequality bounds the dimension of this space of sections, the $\min$ term measuring the rank of the $\#\iota$ node conditions. It is used in the construction of prolongations along a split datum, in [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_mem_riemannRochSpace_ord_residue_eq_neg_of_splitDatum`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_mem_riemannRochSpace_ord_residue_eq_neg_of_splitDatum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_finrank_twistedNodeCompatible_add_min_card_le_of_ringEquiv_ratFunc.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.finrank_twistedNodeCompatible_add_min_card_le_of_ringEquiv_ratFunc
    {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
    (e : RatFunc k ≃+* F) (he : ∀ c : k, e (algebraMap k (RatFunc k) c) = algebraMap k F c)
    {ι : Type*} [Fintype ι]
    (E₁ E₂ : Divisor k F) (hE₁ : -1 ≤ E₁.degree) (hE₂ : -1 ≤ E₂.degree)
    (a b : ι → k) (ha : Function.Injective a) (hb : Function.Injective b)
    (lam : ι → k) (hlam : ∀ i, lam i ≠ 0)
    (T : Submodule k (F × F))
    (hT : ∀ p, p ∈ T ↔ p.1 ∈ riemannRochSpace E₁ ∧ p.2 ∈ riemannRochSpace E₂ ∧
      ∀ i, ∃ c : k,
        (Place.congrEquiv e he (RationalFunctionField.placeOfPoint k (a i))).HasValue
          (e (RatFunc.X - RatFunc.C (a i)) ^
              (E₁ (Place.congrEquiv e he (RationalFunctionField.placeOfPoint k (a i)))) * p.1)
          (lam i * c) ∧
        (Place.congrEquiv e he (RationalFunctionField.placeOfPoint k (b i))).HasValue
          (e (RatFunc.X - RatFunc.C (b i)) ^
              (E₂ (Place.congrEquiv e he (RationalFunctionField.placeOfPoint k (b i)))) * p.2)
          c) :
    (Module.finrank k T : ℤ) + min (Fintype.card ι : ℤ) (max E₁.degree E₂.degree + 1)
      ≤ (E₁.degree + 1) + (E₂.degree + 1) := by sorry
