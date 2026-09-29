-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_mem_holOn_of_forall_mem_holOn_halfDiscPiece_of_cover
-- name    : CerednikDrinfeld.Omega.mem_holOn_of_forall_mem_holOn_halfDiscPiece_of_cover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/6a900709-8c63-5e7c-b74e-88bbe6ed0e93
-- title:
--   Gluing holomorphic functions along half-disc covers of a tube
-- statement:
--   Let $K$ be an algebraically closed field carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$. Fix $c_0, R_0 \in K$ with $R_0 \neq 0$, a finite set $H \subseteq K$ and a function $\rho : K \to K$ with $\rho(h) \neq 0$ for every $h \in H$, and let $P \subseteq K$ be a set characterised by the condition that $z \in P$ if and only if $v(z - c_0) \le v(R_0)$ and $v(\rho(h)) \le v(z - h)$ for all $h \in H$ (a closed disc with finitely many open discs removed). Let $U, \Lambda$ be finite sets of pairs $(e,r) \in K \times K$, each with $r \neq 0$, and assume that every $z \in P$ satisfies $v(z - e) \le v(r)$ for some $(e,r) \in U$, or $v(r) \le v(z - e)$ for some $(e,r) \in \Lambda$. Let $F : P \to K$ be such that, for each $(e,r) \in U$, the restriction of $F$ to $\{z \in P : v(z-e) \le v(r)\}$ and, for each $(e,r) \in \Lambda$, the restriction of $F$ to $\{z \in P : v(r) \le v(z-e)\}$ lies in `holOn` of that piece, i.e. is the uniform limit of a sequence of rational functions (given as `RatPair`s) that are pole-free on the piece and whose values there are bounded in valuation by $v(b)$ for a single $b \in K$. Then $F \in$ `holOn K P`: $F$ is likewise a uniform limit on all of $P$ of a uniformly bounded sequence of rational functions pole-free on $P$.
--
--   This is a gluing statement for rigid-holomorphic (uniformly approximable by bounded pole-free rational) functions on a tube in the rigid affine line, for covers whose members are each cut out by a single inequality, closed or open, relative to $P$. It serves as the base case of the more general gluing result [`CerednikDrinfeld.Omega.mem_holOn_of_forall_mem_holOn_linearPiece_of_cover`](thm.html#CerednikDrinfeld.Omega.mem_holOn_of_forall_mem_holOn_linearPiece_of_cover), and rests on the two-piece gluing lemma [`CerednikDrinfeld.Omega.mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt`](thm.html#CerednikDrinfeld.Omega.mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt) across a sphere.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_mem_holOn_of_forall_mem_holOn_halfDiscPiece_of_cover.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.mem_holOn_of_forall_mem_holOn_halfDiscPiece_of_cover
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]

    (c₀ R₀ : K) (hR₀ : R₀ ≠ 0) (H : Finset K) (ρ : K → K) (hρ : ∀ h ∈ H, ρ h ≠ 0)
    (P : Set K) (hP : ∀ z : K, z ∈ P ↔ Valued.v (z - c₀) ≤ Valued.v R₀ ∧ ∀ h ∈ H, Valued.v (ρ h) ≤ Valued.v (z - h))

    (U Λ : Finset (K × K)) (hU : ∀ er ∈ U, er.2 ≠ 0) (hΛ : ∀ er ∈ Λ, er.2 ≠ 0)
    (hcov : ∀ z ∈ P, (∃ er ∈ U, Valued.v (z - er.1) ≤ Valued.v er.2) ∨ (∃ er ∈ Λ, Valued.v er.2 ≤ Valued.v (z - er.1)))

    (F : ↥P → K)
    (hFU : ∀ er ∈ U, (fun z : ↥{z : K | z ∈ P ∧ Valued.v (z - er.1) ≤ Valued.v er.2} => F ⟨(z : K), z.2.1⟩) ∈
        holOn K {z : K | z ∈ P ∧ Valued.v (z - er.1) ≤ Valued.v er.2})
    (hFΛ : ∀ er ∈ Λ, (fun z : ↥{z : K | z ∈ P ∧ Valued.v er.2 ≤ Valued.v (z - er.1)} => F ⟨(z : K), z.2.1⟩) ∈
        holOn K {z : K | z ∈ P ∧ Valued.v er.2 ≤ Valued.v (z - er.1)}) :
    F ∈ holOn K P := by sorry
