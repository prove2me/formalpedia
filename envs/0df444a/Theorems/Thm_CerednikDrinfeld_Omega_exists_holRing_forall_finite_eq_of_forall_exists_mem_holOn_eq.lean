-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_holRing_forall_finite_eq_of_forall_exists_mem_holOn_eq
-- name    : CerednikDrinfeld.Omega.exists_holRing_forall_finite_eq_of_forall_exists_mem_holOn_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/85d3a6eb-e7a2-5e8c-afa9-c7083d5a70fe
-- title:
--   Gluing generic agreement on affinoids into a global holomorphic function
-- statement:
--   Let $K_0$ be a field and $K$ a field extension of it which carries a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, and which is complete and algebraically closed. Let $\varpi$ be a pseudo-uniformiser of $K$ over $K_0$, that is an element $\varpi \in K_0$ with $0 < v(\varpi) < 1$ in $K$ such that for every $a \in K_0^{\times}$ there is $N$ with $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$. Assume a rank-one condition `hrk`: whenever $x, y \in K$ with $v(x) < 1$ and $y \ne 0$, there is $n \in \mathbb{N}$ with $v(x)^n \le v(y)$. Assume moreover `hex`, that the affinoids $\Omega_n =$ `affinoid` $\varpi\, n$, consisting of the $z \in K$ with $v(z) \le v(\varpi)^{-n}$ and $v(z - a) \ge v(\varpi)^{n}$ for every $a \in K_0$ with $v(a) \le v(\varpi)^{-n}$, exhaust the Drinfeld upper half-plane $\Omega = K \setminus \operatorname{im}(K_0 \to K)$. Let $\Psi : \Omega \to K$ be any function such that for every $n$ there exist a function $\psi$ on $\Omega_n$ lying in `holOn K` $\Omega_n$ — the subring of uniform limits on $\Omega_n$ of sequences of rational functions, each free of poles on $\Omega_n$ and with values of valuation bounded uniformly by some $v(b)$ — and a finite set $Z \subseteq \Omega_n$ with $\Psi(z) = \psi(z)$ for all $z \in \Omega_n \setminus Z$. The conclusion is that there exists $\Phi$ in `holRing` $\varpi$, i.e. a function $\Omega \to K$ whose restriction to each $\Omega_n$ belongs to `holOn K` $\Omega_n$, such that for every $n$ there is a finite $Z \subseteq \Omega_n$ with $\Psi(z) = \Phi(z)$ for all $z \in \Omega_n \setminus Z$.
--
--   This is the gluing step for the Stein exhaustion of Drinfeld's upper half-plane: local data given on each affinoid $\Omega_n$ only up to finitely many exceptional points assemble into a single global rigid-analytic function agreeing with $\Psi$ outside a finite subset of each $\Omega_n$. It is used, via the equivariant refinement [`CerednikDrinfeld.Omega.exists_holRing_forall_finite_mul_eq_of_forall_exists_mem_holOn_affinoid_mul_eq_of_invariant`](thm.html#CerednikDrinfeld.Omega.exists_holRing_forall_finite_mul_eq_of_forall_exists_mem_holOn_affinoid_mul_eq_of_invariant), to produce global holomorphic functions satisfying a prescribed transformation law; the proof cites the identity principle for functions holomorphic on a disc, [`CerednikDrinfeld.Omega.finite_setOf_apply_eq_zero_disc_of_mem_holOn`](thm.html#CerednikDrinfeld.Omega.finite_setOf_apply_eq_zero_disc_of_mem_holOn).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_holRing_forall_finite_eq_of_forall_exists_mem_holOn_eq.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_holRing_forall_finite_eq_of_forall_exists_mem_holOn_eq
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (Ψ : ↥(upperHalfPlane K₀ K) → K)
    (h : ∀ n : ℕ, ∃ ψ : ↥(affinoid ϖ n) → K, ψ ∈ holOn K (affinoid ϖ n) ∧
      ∃ Z : Set ↥(affinoid ϖ n), Z.Finite ∧
        ∀ z : ↥(affinoid ϖ n), z ∉ Z → Ψ ⟨(z : K), affinoid_subset_upperHalfPlane ϖ n z.2⟩ = ψ z) :
    ∃ Φ : ↥(holRing ϖ), ∀ n : ℕ, ∃ Z : Set ↥(affinoid ϖ n), Z.Finite ∧
      ∀ z : ↥(affinoid ϖ n), z ∉ Z →
        Ψ ⟨(z : K), affinoid_subset_upperHalfPlane ϖ n z.2⟩ =
          (Φ : ↥(upperHalfPlane K₀ K) → K) ⟨(z : K), affinoid_subset_upperHalfPlane ϖ n z.2⟩ := by sorry
