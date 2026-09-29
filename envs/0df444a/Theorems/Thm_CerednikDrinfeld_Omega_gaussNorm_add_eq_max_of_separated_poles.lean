-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_gaussNorm_add_eq_max_of_separated_poles
-- name    : CerednikDrinfeld.Omega.gaussNorm_add_eq_max_of_separated_poles
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/b6b36bf3-f251-5a37-9403-f8248992c820
-- title:
--   Gauss norm of a sum with separated poles
-- statement:
--   Let $K$ be an algebraically closed field equipped with a valuation $v$ taking values in a linearly ordered commutative group with zero $\Gamma_0$, and let $P_A,Q_A,P_B,Q_B\in K[X]$ with $Q_A\neq 0$, $Q_B\neq 0$ and $\deg P_A<\deg Q_A$. Assume that one of the following two alternatives holds: either every root $\alpha$ of $Q_A$ (counted in its multiset of roots in $K$) satisfies $v(\alpha)<1$ and every root $\beta$ of $Q_B$ satisfies $1\le v(\beta)$; or every root $\alpha$ of $Q_A$ satisfies $v(\alpha)\le 1$ and every root $\beta$ of $Q_B$ satisfies $1<v(\beta)$. For a polynomial $P$ write $\|P\|$ for the supremum, over the indices $i$ in the support of $P$, of $v(P_i)$ where $P_i$ is the $i$-th coefficient — that is, the Gauss norm, the largest valuation of a nonzero coefficient, with the supremum over the empty support equal to $0$. The conclusion is the equality $$\|P_AQ_B+P_BQ_A\| = \max\bigl(\|P_AQ_B\|,\ \|P_BQ_A\|\bigr),$$ so that no cancellation of the Gauss norm occurs between the two products.
--
--   Read through multiplicativity of the Gauss norm and its identification with the supremum norm on the unit circle, this is the norm statement accompanying a Mittag–Leffler (partial fraction) decomposition across the unit circle: the component $P_A/Q_A$, a proper fraction with all poles in the open (respectively closed) unit disc, and the component $P_B/Q_B$, with no pole there, are orthogonal for the Gauss norm. It is used in the analysis of rational functions on annuli and affinoid subsets of the $p$-adic upper half plane, notably in the identity principle on an annulus and in the estimates for values of pairs of rational functions on spheres and pole-free affinoids.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_gaussNorm_add_eq_max_of_separated_poles.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.Omega.gaussNorm_add_eq_max_of_separated_poles
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (PA QA PB QB : Polynomial K) (hQA : QA ≠ 0) (hQB : QB ≠ 0) (hdeg : PA.degree < QA.degree)
    (h : ((∀ α ∈ QA.roots, Valued.v α < 1) ∧ ∀ β ∈ QB.roots, 1 ≤ Valued.v β) ∨
      ((∀ α ∈ QA.roots, Valued.v α ≤ 1) ∧ ∀ β ∈ QB.roots, 1 < Valued.v β)) :
    (PA * QB + PB * QA).support.sup (fun i => Valued.v ((PA * QB + PB * QA).coeff i)) =
      max ((PA * QB).support.sup fun i => Valued.v ((PA * QB).coeff i))
        ((PB * QA).support.sup fun i => Valued.v ((PB * QA).coeff i)) := by sorry
