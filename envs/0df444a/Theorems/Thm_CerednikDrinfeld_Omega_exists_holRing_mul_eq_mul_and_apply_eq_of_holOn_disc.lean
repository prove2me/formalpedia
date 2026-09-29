-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_holRing_mul_eq_mul_and_apply_eq_of_holOn_disc
-- name    : CerednikDrinfeld.Omega.exists_holRing_mul_eq_mul_and_apply_eq_of_holOn_disc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/3a381e20-7df1-5564-8993-5a2b4c7724a1
-- title:
--   Value of A/B at a point of local holomorphic quotient
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra which is a field, carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, and assume: for all $x,y\in K$ with $v(x)<1$ and $y\neq 0$ there is $n\in\mathbb N$ with $v(x)^n\le v(y)$; $K$ is complete and algebraically closed. Let $\varpi$ be a pseudo-uniformiser, i.e. an element $\varpi\in K_0$ with $0<v(\varpi)<1$ such that every nonzero $a\in K_0$ satisfies $v(\varpi)^N\le v(a)\le v(\varpi)^{-N}$ for some $N$, and assume it is exhausting: every point of $\Omega:=K\setminus\operatorname{im}(K_0\to K)$ lies in one of the affinoids $\{z: v(z)\le v(\varpi)^{-n}$ and $v(z-a)\ge v(\varpi)^{n}$ for all $a\in K_0$ with $v(a)\le v(\varpi)^{-n}\}$; assume further that for each $n$ there is a finite $T\subseteq K_0$ with every $a\in K_0$, $v(a)\le v(\varpi)^{-n}$, satisfying $v(a-t)<v(\varpi)^n$ for some $t\in T$. Let $A,B$ lie in `Omega.holRing` $\varpi$ — functions $\Omega\to K$ whose restriction to each affinoid is a uniform limit of uniformly bounded rational functions without poles there — with $B\neq 0$; let $z\in\Omega$, $N\in\mathbb N$, and let $D=\{w\in K: v(w-z)\le v(\varpi)^N\}$ be contained in $\Omega$. Let $a,b:D\to K$ belong to `Omega.holOn` $K\,D$ (uniform limits on $D$ of uniformly bounded pole-free rational functions), with $b(w)\neq 0$ for every $w\in D$ with $w=z$, and suppose there is a finite subset $Z\subseteq D$ with $B(w)\,a(w)=A(w)\,b(w)$ for all $w\in D\setminus Z$. Then there exist $G,H$ in `Omega.holRing` $\varpi$ with $H(z)\neq 0$, $A\,H=B\,G$ as elements of that ring, and $G(z)\,b(w)=H(z)\,a(w)$ for every $w\in D$ with $w=z$.
--
--   This says that the meromorphic function $A/B$ on the Drinfeld upper half-plane is regular at $z$ with value $a(z)/b(z)$, presented in the form of a global equality $AH=BG$ with $H(z)\neq 0$ together with the matching of values at $z$. It is used in identifying the function field of a Čerednik–Drinfeld quotient with a field of invariants, where a rigid-holomorphic quotient given locally on a disc must be recognised as the value of a globally defined ratio.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_holRing_mul_eq_mul_and_apply_eq_of_holOn_disc.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_holRing_mul_eq_mul_and_apply_eq_of_holOn_disc
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    [CompleteSpace K] [IsAlgClosed K]
    (ϖ : Omega.PseudoUniformizer K₀ K) (hex : Omega.IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (A B : ↥(Omega.holRing ϖ)) (hB : B ≠ 0) (z : ↥(Omega.upperHalfPlane K₀ K)) (N : ℕ)
    (hD : {w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N} ⊆ Omega.upperHalfPlane K₀ K)
    (a b : ↥{w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N} → K)
    (ha : a ∈ Omega.holOn K {w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N}) (hb : b ∈ Omega.holOn K {w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N})
    (hbz : ∀ w : ↥{w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N}, (w : K) = (z : K) → b w ≠ 0)
    (heq : ∃ Z : Set ↥{w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N}, Z.Finite ∧ ∀ w : ↥{w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N}, w ∉ Z →
      (B : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨(w : K), hD w.2⟩ * a w = (A : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨(w : K), hD w.2⟩ * b w) :
    ∃ G H : ↥(Omega.holRing ϖ), (H : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 ∧ A * H = B * G ∧
      ∀ w : ↥{w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N}, (w : K) = (z : K) →
        (G : ↥(Omega.upperHalfPlane K₀ K) → K) z * b w = (H : ↥(Omega.upperHalfPlane K₀ K) → K) z * a w := by sorry
