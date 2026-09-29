-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_mem_holOn_of_forall_mem_holOn_linearPiece_of_cover
-- name    : CerednikDrinfeld.Omega.mem_holOn_of_forall_mem_holOn_linearPiece_of_cover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/eda5e958-02d3-57f5-a1e1-a680adc84c3f
-- title:
--   Gluing rigid-holomorphic functions along finite linear covers
-- statement:
--   Let $K$ be a field, complete and algebraically closed, with a valuation $v$ taking values in a linearly ordered commutative group with zero $\Gamma_0$, subject to two compatibility hypotheses: for all $x,y\in K$ with $v(x)<1$ and $y\neq 0$ there is $n\in\mathbb{N}$ with $v(x)^n\le v(y)$, and for every $\varepsilon\neq 0$ in $\Gamma_0$ there is $y\in K$, $y\neq 0$, with $v(y)\le\varepsilon$. Let $c_0,R_0\in K$ with $R_0\neq 0$, let $H\subset K$ be finite, and let $\rho:K\to K$ satisfy $\rho(h)\neq 0$ for $h\in H$; let $P\subseteq K$ be a set characterised by $z\in P$ if and only if $v(z-c_0)\le v(R_0)$ and $v(\rho(h))\le v(z-h)$ for all $h\in H$. Let $\iota$ be a finite type and $L,M:\iota\to$ finite sets of pairs $(e,r)\in K\times K$, all second coordinates nonzero, and put $P_i=\{z\in P: v(r)\le v(z-e)\ \text{for }(e,r)\in L_i,\ v(z-e)\le v(r)\ \text{for }(e,r)\in M_i\}$; assume every $z\in P$ lies in some $P_i$. Let $F:P\to K$ be such that for each $i$ the restriction of $F$ to $P_i$ lies in `holOn K P_i`, i.e. is a uniform limit on $P_i$ of a sequence of rational functions, each pole-free on $P_i$ and all bounded in valuation by a single $b\in K$. Then $F$ itself is such a uniform limit of uniformly bounded pole-free rational functions on $P$, i.e. $F\in$ `holOn K P`.
--
--   This is the sheaf property (Tate acyclicity) for rigid-holomorphic functions on a disc with finitely many holes, in the elementary case of a finite covering by rational subdomains cut out by linear inequalities $v(z-e)\le v(r)$ and $v(r)\le v(z-e)$. It feeds the construction of rigid-holomorphic functions on $\Omega$ from local data, being used in [`CerednikDrinfeld.Omega.exists_polynomial_ne_zero_mul_mem_holOn_of_forall_mem_holOn_mul_eq_linearPiece_cover`](thm.html#CerednikDrinfeld.Omega.exists_polynomial_ne_zero_mul_mem_holOn_of_forall_mem_holOn_mul_eq_linearPiece_cover), and it is reduced by the proof to the two-piece Laurent case via [`CerednikDrinfeld.Omega.mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt`](thm.html#CerednikDrinfeld.Omega.mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt) and [`CerednikDrinfeld.Omega.mem_holOn_of_forall_mem_holOn_halfDiscPiece_of_cover`](thm.html#CerednikDrinfeld.Omega.mem_holOn_of_forall_mem_holOn_halfDiscPiece_of_cover).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_mem_holOn_of_forall_mem_holOn_linearPiece_of_cover.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.mem_holOn_of_forall_mem_holOn_linearPiece_of_cover
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hval : ∀ ε : Γ₀, ε ≠ 0 → ∃ y : K, y ≠ 0 ∧ Valued.v y ≤ ε)

    (c₀ R₀ : K) (hR₀ : R₀ ≠ 0) (H : Finset K) (ρ : K → K) (hρ : ∀ h ∈ H, ρ h ≠ 0)
    (P : Set K) (hP : ∀ z : K, z ∈ P ↔ Valued.v (z - c₀) ≤ Valued.v R₀ ∧ ∀ h ∈ H, Valued.v (ρ h) ≤ Valued.v (z - h))

    {ι : Type} [Fintype ι] (L M : ι → Finset (K × K))
    (hL : ∀ i, ∀ er ∈ L i, er.2 ≠ 0) (hM : ∀ i, ∀ er ∈ M i, er.2 ≠ 0)
    (hcov : ∀ z ∈ P, ∃ i, (∀ er ∈ L i, Valued.v er.2 ≤ Valued.v (z - er.1)) ∧ (∀ er ∈ M i, Valued.v (z - er.1) ≤ Valued.v er.2))

    (F : ↥P → K)
    (hF : ∀ i, (fun z : ↥{z : K | z ∈ P ∧ (∀ er ∈ L i, Valued.v er.2 ≤ Valued.v (z - er.1)) ∧
          (∀ er ∈ M i, Valued.v (z - er.1) ≤ Valued.v er.2)} => F ⟨(z : K), z.2.1⟩) ∈
        holOn K {z : K | z ∈ P ∧ (∀ er ∈ L i, Valued.v er.2 ≤ Valued.v (z - er.1)) ∧
          (∀ er ∈ M i, Valued.v (z - er.1) ≤ Valued.v er.2)}) :
    F ∈ holOn K P := by sorry
