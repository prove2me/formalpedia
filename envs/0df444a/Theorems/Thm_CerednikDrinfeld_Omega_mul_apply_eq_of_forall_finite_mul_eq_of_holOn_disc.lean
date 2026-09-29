-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_mul_apply_eq_of_forall_finite_mul_eq_of_holOn_disc
-- name    : CerednikDrinfeld.Omega.mul_apply_eq_of_forall_finite_mul_eq_of_holOn_disc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/dfc1e3bf-9ffc-52af-878b-6c4ebecfef1e
-- title:
--   Identity principle: global relation HF=Φ holds at a point with local presentation
-- statement:
--   Let $K_0$ be a field and $K$ a field that is a $K_0$-algebra, equipped with a valuation $v =$ `Valued.v` into a linearly ordered commutative group with zero $\Gamma_0$, with $K$ complete and algebraically closed; let $\varpi$ be a pseudo-uniformiser, i.e. an element $\varpi \in K_0$ with $0 < v(\varpi) < 1$ in $K$ and such that every non-zero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N$. Assume the rank-one condition `hrk`: whenever $v(x) < 1$ and $y \ne 0$ there is $n$ with $v(x)^n \le v(y)$; and assume `hex`, that every point of the Drinfeld upper half plane $\Omega = K \setminus \operatorname{im}(K_0 \to K)$ lies in one of the affinoids $\Omega_n = \{z : v(z) \le v(\varpi)^{-n}$ and $v(z - a) \ge v(\varpi)^{n}$ for all $a \in K_0$ with $v(a) \le v(\varpi)^{-n}\}$. Let $F : \Omega \to K$ be an arbitrary function and let $\Phi, H$ lie in the ring of functions on $\Omega$ whose restriction to each $\Omega_n$ is a uniform limit of uniformly bounded rational functions without poles on $\Omega_n$. Assume that for every $n$ there is a finite subset $Z \subseteq \Omega_n$ with $H(z)F(z) = \Phi(z)$ for all $z \in \Omega_n \setminus Z$. Finally fix $z \in \Omega$ and $N \in \mathbb{N}$ such that the closed disc $D = \{w : v(w - z) \le v(\varpi)^N\}$ is contained in $\Omega$, and functions $a, b : D \to K$ in the corresponding ring of holomorphic functions on $D$, with $b(w) \ne 0$ for every $w \in D$ having $w = z$, and $b(w)F(w) = a(w)$ for all $w \in D$. Then $H(z)F(z) = \Phi(z)$.
--
--   This is an identity-principle step for rigid-holomorphic functions on Drinfeld's $p$-adic upper half plane: a multiplicative relation between a holomorphic pair $(H,\Phi)$ and an arbitrary function $F$, valid on each affinoid away from a finite set, propagates to any point at which $F$ admits a local presentation $F = a/b$ with $b$ non-vanishing. It is used in the construction of the ring homomorphism from the function field of the Mumford curve into the invariant field, where chartwise meromorphic functions have to be evaluated pointwise.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_mul_apply_eq_of_forall_finite_mul_eq_of_holOn_disc.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.mul_apply_eq_of_forall_finite_mul_eq_of_holOn_disc
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (F : ↥(upperHalfPlane K₀ K) → K) (Φ H : ↥(holRing ϖ))
    (hHF : ∀ n : ℕ, ∃ Z : Set ↥(affinoid ϖ n), Z.Finite ∧ ∀ z : ↥(affinoid ϖ n), z ∉ Z →
      (H : ↥(upperHalfPlane K₀ K) → K) ⟨(z : K), affinoid_subset_upperHalfPlane ϖ n z.2⟩ *
          F ⟨(z : K), affinoid_subset_upperHalfPlane ϖ n z.2⟩ =
        (Φ : ↥(upperHalfPlane K₀ K) → K) ⟨(z : K), affinoid_subset_upperHalfPlane ϖ n z.2⟩)
    (z : ↥(upperHalfPlane K₀ K)) (N : ℕ)
    (hD : {w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N} ⊆ upperHalfPlane K₀ K)
    (a b : ↥{w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N} → K)
    (ha : a ∈ holOn K {w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N})
    (hb : b ∈ holOn K {w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N})
    (hbz : ∀ w : ↥{w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N}, (w : K) = (z : K) → b w ≠ 0)
    (hab : ∀ w : ↥{w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N}, b w * F ⟨(w : K), hD w.2⟩ = a w) :
    (H : ↥(upperHalfPlane K₀ K) → K) z * F z = (Φ : ↥(upperHalfPlane K₀ K) → K) z := by sorry
