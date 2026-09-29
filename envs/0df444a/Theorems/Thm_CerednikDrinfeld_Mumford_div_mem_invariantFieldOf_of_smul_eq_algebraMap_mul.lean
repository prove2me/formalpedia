-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_div_mem_invariantFieldOf_of_smul_eq_algebraMap_mul
-- name    : CerednikDrinfeld.Mumford.div_mem_invariantFieldOf_of_smul_eq_algebraMap_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/e04368bd-07a7-583b-b66a-ad30969ef58c
-- title:
--   Quotient of two u-eigenvectors lies in the Γ-invariant field
-- statement:
--   Let $K$ be a field, $G$ a group, and $M$ a commutative $K$-algebra which is a domain, equipped with an action of $G$ by ring automorphisms commuting with the $K$-algebra structure (a `MulSemiringAction G M` together with `SMulCommClass G K M`), so that $G$ acts on the fraction field $\operatorname{Frac} M$ as well. Let $\Gamma$ be a subgroup of $G$, let $u : G \to K$ be an arbitrary function (no multiplicativity is assumed), and let $x, y \in \operatorname{Frac} M$ satisfy the two automorphy conditions $\gamma \cdot x = u(\gamma)\,x$ and $\gamma \cdot y = u(\gamma)\,y$ for every $\gamma \in \Gamma$, where $u(\gamma)$ acts through the structure map $K \to \operatorname{Frac} M$. The conclusion is that $x / y$ belongs to `invariantFieldOf K G M Γ`, that is, to the subfield of $\operatorname{Frac} M$ consisting of those elements $z$ with $\gamma \cdot z = z$ for all $\gamma \in \Gamma$. No nonvanishing hypothesis on $u$, on $x$ or on $y$ is imposed; in particular the degenerate cases are covered by the convention $z/0 = 0$.
--
--   This is the algebraic mechanism behind the passage from theta functions with an automorphy factor to genuine functions on a Mumford quotient: a ratio of two eigen-elements with the same multiplier system descends to the field of $\Gamma$-invariants. It is used in the construction of periods and in the recognition of principal divisors on the quotient curve, via [`AlgebraicCurve.Pic0.exists_prod_theta_eq_period_of_isPrincipal_of_v_card_stabilizer_eq_one`](thm.html#AlgebraicCurve.Pic0.exists_prod_theta_eq_period_of_isPrincipal_of_v_card_stabilizer_eq_one) and [`AlgebraicCurve.Pic0.isPrincipal_sum_sub_sum_of_prod_theta_eq_of_v_card_stabilizer_eq_one`](thm.html#AlgebraicCurve.Pic0.isPrincipal_sum_sub_sum_of_prod_theta_eq_of_v_card_stabilizer_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_div_mem_invariantFieldOf_of_smul_eq_algebraMap_mul.lean

import Definitions.Def_CerednikDrinfeld_MumfordQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.div_mem_invariantFieldOf_of_smul_eq_algebraMap_mul
    (K : Type) [Field K] (G : Type) [Group G] (M : Type) [CommRing M] [Algebra K M]
    [MulSemiringAction G M] [SMulCommClass G K M] [IsDomain M]
    (Γ : Subgroup G) (u : G → K) (x y : FractionRing M)
    (hx : ∀ γ : G, γ ∈ Γ → γ • x = algebraMap K (FractionRing M) (u γ) * x)
    (hy : ∀ γ : G, γ ∈ Γ → γ • y = algebraMap K (FractionRing M) (u γ) * y) :
    x / y ∈ invariantFieldOf K G M Γ := by sorry
