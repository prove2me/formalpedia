-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_ordAt_mul
-- name    : CerednikDrinfeld.Omega.ordAt_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/ee5da4a1-3e0c-55e5-8e15-05323fddce21
-- title:
--   Additivity of the order of vanishing on Ω
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra which is a field, carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, and assume $K$ is complete and algebraically closed. Let $\varpi$ be a pseudo-uniformizer, i.e. an element $\varpi.\varpi \in K_0$ with $0 < v(\varpi.\varpi) < 1$ in $K$ such that every nonzero $a \in K_0$ satisfies $v(\varpi.\varpi)^N \le v(a) \le v(\varpi.\varpi)^{-N}$ for some $N$. Three further hypotheses are imposed: `hrk`, that for all $x, y \in K$ with $v(x) < 1$ and $y \ne 0$ there is $n$ with $v(x)^n \le v(y)$; `hex`, that every point of the Drinfeld upper half plane $\Omega = K \setminus \mathrm{image}(K_0 \to K)$ lies in one of the affinoids `affinoid ϖ n`; and `hfin`, that for each $n$ there is a finite $T \subseteq K_0$ such that every $a \in K_0$ with $v(a) \le v(\varpi.\varpi)^{-n}$ satisfies $v(a - t) < v(\varpi.\varpi)^{n}$ for some $t \in T$. Then for nonzero $F, G$ in the ring `holRing ϖ` of functions $\Omega \to K$ whose restriction to each affinoid is a uniform limit of a uniformly bounded sequence of pole-free rational functions, and for $z \in \Omega$, the natural numbers $\operatorname{ord}_z(H) = \sup\{n : (\mathrm{coord} - z)^n \mid H\}$ satisfy $\operatorname{ord}_z(FG) = \operatorname{ord}_z(F) + \operatorname{ord}_z(G)$.
--
--   This is the additivity of the order of vanishing for rigid-holomorphic functions on Drinfeld's upper half plane, the multiplicative property making $\operatorname{ord}_z$ into a divisor-valued invariant. It is used downstream in the study of divisors of theta functions and of principal divisors on the associated quotient curves, and in the criterion that a function divisible at each point to the prescribed order is divisible by the corresponding product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_ordAt_mul.lean

import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.ordAt_mul
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (F G : ↥(holRing ϖ)) (hF : F ≠ 0) (hG : G ≠ 0) (z : ↥(upperHalfPlane K₀ K)) :
    ordAt ϖ (F * G) z = ordAt ϖ F z + ordAt ϖ G z := by sorry
