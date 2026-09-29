-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_polynomial_ne_zero_mul_mem_holOn_of_forall_mem_holOn_mul_eq_linearPiece_cover
-- name    : CerednikDrinfeld.Omega.exists_polynomial_ne_zero_mul_mem_holOn_of_forall_mem_holOn_mul_eq_linearPiece_cover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/b16038ad-3691-5053-a59c-7ae6ee0b7f71
-- title:
--   Polynomial clearing of a piecewise meromorphic function on a tube
-- statement:
--   Let $K$ be a field with a valuation $v$ taking values in a linearly ordered commutative group with zero $\Gamma_0$, complete and algebraically closed, and assume: (hrk) for all $x,y \in K$ with $v(x) < 1$ and $y \neq 0$ there is $n \in \mathbb{N}$ with $v(x)^n \le v(y)$; (hval) every non-zero $\varepsilon \in \Gamma_0$ satisfies $v(y) \le \varepsilon$ for some $y \neq 0$; (hnt) there is $y \neq 0$ with $v(y) < 1$. Let $c_0, R_0 \in K$ with $R_0 \neq 0$, let $H \subseteq K$ be finite, let $\rho : K \to K$ be non-vanishing on $H$, and let $P \subseteq K$ be a set characterised by $z \in P \iff v(z-c_0) \le v(R_0)$ and $v(\rho(h)) \le v(z-h)$ for all $h \in H$. Let $\iota$ be a finite type and $L, M : \iota \to$ Finset$(K \times K)$ with all second coordinates non-zero, and put $P_i = \{ z \in P : v(r) \le v(z-e) \text{ for } (e,r) \in L_i,\ v(z-e) \le v(r) \text{ for } (e,r) \in M_i \}$; assume the $P_i$ cover $P$. Let $F : P \to K$ be an arbitrary function, $E \subseteq K$ a finite set, and for each $i$ let $f_i, g_i : P_i \to K$ lie in `holOn K P_i`, i.e. be uniform limits on $P_i$ of sequences of rational functions that are pole-free on $P_i$ and uniformly bounded in absolute value by the value of a single element of $K$; assume each $g_i$ has finitely many zeros on $P_i$, and that $g_i(z) F(z) = f_i(z)$ for every $z \in P_i$ with $z \notin E$. Then there is a non-zero polynomial $b \in K[X]$ such that $z \mapsto b(z) F(z)$ belongs to `holOn K P`.
--
--   This is the gluing-and-denominator-clearing step for rigid-analytic functions on a tube (a closed disc with finitely many open discs removed): a function given piecewise as a quotient of holomorphic functions on a finite cover by linear pieces becomes holomorphic on the whole tube after multiplication by one polynomial. It is used in the Čerednik–Drinfeld part of the development, in the construction of holomorphic functions on edge regions of the quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_polynomial_ne_zero_mul_mem_holOn_of_forall_mem_holOn_mul_eq_linearPiece_cover.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_polynomial_ne_zero_mul_mem_holOn_of_forall_mem_holOn_mul_eq_linearPiece_cover
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hval : ∀ ε : Γ₀, ε ≠ 0 → ∃ y : K, y ≠ 0 ∧ Valued.v y ≤ ε)
    (hnt : ∃ y : K, y ≠ 0 ∧ Valued.v y < 1)

    (c₀ R₀ : K) (hR₀ : R₀ ≠ 0) (H : Finset K) (ρ : K → K) (hρ : ∀ h ∈ H, ρ h ≠ 0)
    (P : Set K) (hP : ∀ z : K, z ∈ P ↔ Valued.v (z - c₀) ≤ Valued.v R₀ ∧ ∀ h ∈ H, Valued.v (ρ h) ≤ Valued.v (z - h))

    {ι : Type} [Fintype ι] (L M : ι → Finset (K × K))
    (hL : ∀ i, ∀ er ∈ L i, er.2 ≠ 0) (hM : ∀ i, ∀ er ∈ M i, er.2 ≠ 0)
    (hcov : ∀ z ∈ P, ∃ i, (∀ er ∈ L i, Valued.v er.2 ≤ Valued.v (z - er.1)) ∧ (∀ er ∈ M i, Valued.v (z - er.1) ≤ Valued.v er.2))

    (F : ↥P → K) (E : Finset K)
    (f g : (i : ι) → ↥{z : K | z ∈ P ∧ (∀ er ∈ L i, Valued.v er.2 ≤ Valued.v (z - er.1)) ∧
          (∀ er ∈ M i, Valued.v (z - er.1) ≤ Valued.v er.2)} → K)
    (hf : ∀ i, f i ∈ holOn K {z : K | z ∈ P ∧ (∀ er ∈ L i, Valued.v er.2 ≤ Valued.v (z - er.1)) ∧
          (∀ er ∈ M i, Valued.v (z - er.1) ≤ Valued.v er.2)})
    (hg : ∀ i, g i ∈ holOn K {z : K | z ∈ P ∧ (∀ er ∈ L i, Valued.v er.2 ≤ Valued.v (z - er.1)) ∧
          (∀ er ∈ M i, Valued.v (z - er.1) ≤ Valued.v er.2)})
    (hgfin : ∀ i, Set.Finite {z : ↥{z : K | z ∈ P ∧ (∀ er ∈ L i, Valued.v er.2 ≤ Valued.v (z - er.1)) ∧
          (∀ er ∈ M i, Valued.v (z - er.1) ≤ Valued.v er.2)} | g i z = 0})
    (hrep : ∀ (i : ι) (z : ↥{z : K | z ∈ P ∧ (∀ er ∈ L i, Valued.v er.2 ≤ Valued.v (z - er.1)) ∧
          (∀ er ∈ M i, Valued.v (z - er.1) ≤ Valued.v er.2)}),
      (z : K) ∉ E → g i z * F ⟨(z : K), z.2.1⟩ = f i z) :
    ∃ b : Polynomial K, b ≠ 0 ∧ (fun z : ↥P => b.eval (z : K) * F z) ∈ holOn K P := by sorry
