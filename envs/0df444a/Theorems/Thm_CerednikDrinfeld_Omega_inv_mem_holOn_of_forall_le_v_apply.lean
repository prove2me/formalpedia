-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_inv_mem_holOn_of_forall_le_v_apply
-- name    : CerednikDrinfeld.Omega.inv_mem_holOn_of_forall_le_v_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/c9c3df39-ca5e-5d27-a3d0-5e3fb6c501e7
-- title:
--   Holomorphic inverse of a function bounded away from zero
-- statement:
--   Let $K$ be a field carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, and let $S \subseteq K$ be a subset. Let $g : S \to K$ belong to the subring $\mathtt{holOn}\ K\ S$ of functions on $S$, that is: there is a sequence $(r_k)_{k \in \mathbb{N}}$ of pairs of polynomials (numerator and denominator) over $K$, each pole-free on $S$, such that the valuations $v(r_k(z))$ of the associated quotients are bounded by $v(b)$ for a single $b \in K$, uniformly in $k$ and in $z \in S$, and such that $z \mapsto r_k(z)$ converges to $g$ uniformly on $S$ as $k \to \infty$ along the at-top filter. Suppose further that $\delta \in K$ is nonzero and that $v(\delta) \le v(g(z))$ for every $z \in S$. Then the function $z \mapsto g(z)^{-1}$ on $S$ again lies in $\mathtt{holOn}\ K\ S$, i.e. it is a uniformly bounded uniform limit on $S$ of quotients of polynomials without poles on $S$.
--
--   This is the statement that a holomorphic function on $S$ which is bounded away from zero is a unit in the ring of holomorphic functions, in the concrete presentation of holomorphy by uniform approximation through pole-free rational functions. It is used in the study of functions on Drinfeld's upper half plane, in particular in the passage from functions that are locally inverted or multiplicatively described on affinoid pieces to globally holomorphic ones.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_inv_mem_holOn_of_forall_le_v_apply.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.inv_mem_holOn_of_forall_le_v_apply
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (S : Set K) {g : ↥S → K} (hg : g ∈ holOn K S)
    (δ : K) (hδ : δ ≠ 0) (hb : ∀ z : ↥S, Valued.v δ ≤ Valued.v (g z)) :
    (fun z : ↥S => (g z)⁻¹) ∈ holOn K S := by sorry
