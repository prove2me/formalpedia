-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_sum_add_eq_zero_of_isUnit_of_forall_v_apply_eq_mul_zpow
-- name    : CerednikDrinfeld.Omega.sum_add_eq_zero_of_isUnit_of_forall_v_apply_eq_mul_zpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/8692dd42-9ed8-5b78-b03f-c74887d5ba0d
-- title:
--   Edge degrees of a unit of 𝒪(Ω) sum to zero
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra which is a field, valued in a linearly ordered commutative group with zero $\Gamma_0$, complete and algebraically closed, and let $\varpi$ be a pseudo-uniformiser: an element $\varpi \in K_0$ with $0 < v(\varpi) < 1$ in $K$ and such that every nonzero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N \in \mathbb{N}$. Assume the rank-one condition `hrk`, that for $x, y \in K$ with $v(x) < 1$ and $y \ne 0$ there is $n$ with $v(x)^n \le v(y)$, and `hunif`, that every $a \in K_0$ has $v(a) \le v(\varpi)$ or $1 \le v(a)$. Let $T$ be a finite subset of $K_0$ whose elements all satisfy $v(t) \le 1$, such that every $a \in K_0$ with $v(a) \le 1$ has $v(a - t) < 1$ for some $t \in T$, and such that distinct $t, t' \in T$ satisfy $1 \le v(t - t')$; thus $T$ is a system of representatives for the residue classes of the valuation ring of $K_0$. Let $f$ be a unit of the ring `holRing` $\varpi$ of functions on $\Omega = K \setminus \operatorname{im}(K_0 \to K)$ whose restriction to each affinoid `affinoid` $\varpi\,n$ is a uniform limit of a uniformly bounded sequence of rational functions without poles there. Let $m : K_0 \to \mathbb{Z}$ and $m_\infty \in \mathbb{Z}$ be such that for each $t \in T$ there is $c \in \Gamma_0$ with $v(f(z)) = c\, v(z - t)^{m(t)}$ for all $z \in \Omega$ with $v(\varpi) < v(z - t) < 1$, and there is $c \in \Gamma_0$ with $v(f(z)) = c\, (v(z)^{-1})^{m_\infty}$ for all $z \in \Omega$ with $v(\varpi) < v(z)^{-1} < 1$. The conclusion is twofold: $\sum_{t \in T} m(t) + m_\infty = 0$, and there is a single $c_0 \in \Gamma_0$ with $v(f(z)) = c_0 \prod_{t \in T} v(z - t)^{m(t)}$ for every $z \in \Omega$ satisfying $v(\varpi) < v(z - t)$ for all $t \in T$ and $v(z) < v(\varpi)^{-1}$.
--
--   This is the harmonicity of the current attached to an invertible rigid-holomorphic function on the Drinfeld upper half plane at the standard vertex: the degrees of $|f|$ on the $q+1$ open annuli leaving that vertex sum to zero, and the monomial descriptions on the separate annuli glue into one product formula on the whole open star. It is stated without reference to the Bruhat–Tits tree, and is used in the construction of the integer-valued harmonic cochain attached to a unit and in the divisibility statement for the degrees of an equivariant unit.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_sum_add_eq_zero_of_isUnit_of_forall_v_apply_eq_mul_zpow.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.sum_add_eq_zero_of_isUnit_of_forall_v_apply_eq_mul_zpow
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (T : Finset K₀) (hT : ∀ t ∈ T, Valued.v (algebraMap K₀ K t) ≤ 1)
    (hTcov : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < 1)
    (hTsep : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → 1 ≤ Valued.v (algebraMap K₀ K t - algebraMap K₀ K t'))
    (f : ↥(holRing ϖ)) (hf : IsUnit f) (m : K₀ → ℤ) (mInf : ℤ)
    (hm : ∀ t ∈ T, ∃ c : Γ₀, ∀ z : ↥(upperHalfPlane K₀ K),
      Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v ((z : K) - algebraMap K₀ K t) →
      Valued.v ((z : K) - algebraMap K₀ K t) < 1 →
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) = c * Valued.v ((z : K) - algebraMap K₀ K t) ^ (m t))
    (hmInf : ∃ c : Γ₀, ∀ z : ↥(upperHalfPlane K₀ K),
      Valued.v (algebraMap K₀ K ϖ.ϖ) < (Valued.v (z : K))⁻¹ → (Valued.v (z : K))⁻¹ < 1 →
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) = c * (Valued.v (z : K))⁻¹ ^ mInf) :
    (∑ t ∈ T, m t) + mInf = 0 ∧
    ∃ c₀ : Γ₀, ∀ z : ↥(upperHalfPlane K₀ K),
      (∀ t ∈ T, Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v ((z : K) - algebraMap K₀ K t)) →
      Valued.v (z : K) < (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ →
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) =
          c₀ * ∏ t ∈ T, Valued.v ((z : K) - algebraMap K₀ K t) ^ (m t) := by sorry
