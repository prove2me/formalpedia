-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_polynomial_ne_zero_forall_mul_mem_holOn_of_forall_exists_mem_holOn_mul_eq_of_polynomial
-- name    : CerednikDrinfeld.Omega.exists_polynomial_ne_zero_forall_mul_mem_holOn_of_forall_exists_mem_holOn_mul_eq_of_polynomial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/39c34da8-7b47-5614-9aaf-204f91fdfa54
-- title:
--   A polynomial clearing denominators simultaneously on finitely many affinoid pieces
-- statement:
--   Let $K_0$ be a field and $K$ a field which is a $K_0$-algebra, equipped with a valuation $v$ taking values in a linearly ordered commutative group with zero $\Gamma_0$. Let $\varpi$ be a `PseudoUniformizer` for $K_0$ in $K$: an element $\varpi \in K_0$ with $0 < v(\varpi) < 1$ in $K$ and such that every non-zero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N \in \mathbb{N}$. Fix $n \in \mathbb{N}$ and write $\Omega_n =$ `affinoid ϖ n` for the set of $z \in K$ with $v(z) \le v(\varpi)^{-n}$ and $v(z - a) \ge v(\varpi)^{n}$ for every $a \in K_0$ with $v(a) \le v(\varpi)^{-n}$. Let $\iota$ be a finite type, let $S_i \subseteq \Omega_n$ for each $i \in \iota$, and let $F : \Omega_n \to K$ be an arbitrary function. Suppose given non-zero polynomials $P_i \in K[X]$ and functions $f_i : S_i \to K$ lying in the subring `holOn K (S i)`, i.e. each $f_i$ is the uniform limit on $S_i$ of a sequence of rational pairs that are pole-free on $S_i$ and whose values are uniformly bounded in valuation by a single $b \in K$; and suppose that for every $i$ and every $z \in S_i$ with $P_i(z) \ne 0$ one has $P_i(z)\,F(z) = f_i(z)$. Then there is a non-zero $g \in K[X]$ such that for every $i$ the function $z \mapsto g(z)\,F(z)$ on $S_i$ lies in `holOn K (S i)`.
--
--   This is the polynomial-denominator clearing step for functions on an affinoid piece of Drinfeld's upper half-plane: local identities $P_i F = f_i$ valid away from the zeros of $P_i$ are upgraded to a single global polynomial multiplier making $gF$ holomorphic on each piece, with no completeness, algebraic closedness or covering hypothesis on $K$ and no regularity assumption on $F$ itself. It is used in [`CerednikDrinfeld.exists_holOn_affinoid_mul_pullback_eq_of_cover_clearing_of_cerednikDrinfeld_quotient`](thm.html#CerednikDrinfeld.exists_holOn_affinoid_mul_pullback_eq_of_cover_clearing_of_cerednikDrinfeld_quotient), where the pieces $S_i$ form a cover of the affinoid.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_polynomial_ne_zero_forall_mul_mem_holOn_of_forall_exists_mem_holOn_mul_eq_of_polynomial.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_polynomial_ne_zero_forall_mul_mem_holOn_of_forall_exists_mem_holOn_mul_eq_of_polynomial
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : PseudoUniformizer K₀ K) (n : ℕ)
    {ι : Type} [Fintype ι] (S : ι → Set K) (hS : ∀ i, S i ⊆ affinoid ϖ n)
    (F : ↥(affinoid ϖ n) → K)
    (P : ι → Polynomial K) (hP : ∀ i, P i ≠ 0)
    (f : (i : ι) → ↥(S i) → K) (hf : ∀ i, f i ∈ holOn K (S i))
    (hrep : ∀ (i : ι) (z : ↥(S i)), (P i).eval (z : K) ≠ 0 → (P i).eval (z : K) * F ⟨(z : K), hS i z.2⟩ = f i z) :
    ∃ g : Polynomial K, g ≠ 0 ∧
      ∀ i : ι, (fun z : ↥(S i) => g.eval (z : K) * F ⟨(z : K), hS i z.2⟩) ∈ holOn K (S i) := by sorry
