-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_mul_prod_zpow_mul_one_add_of_isUnit
-- name    : CerednikDrinfeld.Omega.exists_eq_mul_prod_zpow_mul_one_add_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/631488c9-b268-594f-a23f-7256b2014165
-- title:
--   Normal form for units of 𝒪(Ω) on the standard star
-- statement:
--   Let $K_0$ be a field and $K$ a complete, algebraically closed extension field of $K_0$ carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$. Let $\varpi$ be a pseudo-uniformiser, i.e. an element $\varpi \in K_0$ with $0 < v(\varpi) < 1$ in $K$ such that every nonzero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N$; write $\mathfrak p = v(\varpi)$. Assume: $v$ has rank one in the sense that for all $x, y \in K$ with $v(x) < 1$ and $y \neq 0$ there is $n$ with $v(x)^n \le v(y)$ (`hrk`); $\varpi$ is a uniformiser for $K_0$, i.e. each $a \in K_0$ has $v(a) \le \mathfrak p$ or $v(a) \ge 1$ (`hunif`); and $T$ is a finite subset of $K_0$ whose elements have $v(t) \le 1$, which meets every residue class ($v(a) \le 1$ implies $v(a - t) < 1$ for some $t \in T$) and is separated ($1 \le v(t - t')$ for distinct $t, t' \in T$). Let $f$ be a unit of the ring $\mathcal{O}(\Omega)$ of functions on $\Omega = K \setminus K_0$ that are holomorphic on every affinoid $\{z : v(z) \le \mathfrak p^{-n},\ v(z - a) \ge \mathfrak p^{n} \text{ for all } a \in K_0 \text{ with } v(a) \le \mathfrak p^{-n}\}$, holomorphy meaning uniform approximation there by rational functions without poles on the affinoid, with valuations uniformly bounded. Then there are $c \in K$ with $c \neq 0$, integers $m_t$ indexed by $K_0$, and $h \in \mathcal{O}(\Omega)$ such that on the open star $S = \{z \in \Omega : v(z - t) > \mathfrak p \text{ for all } t \in T,\ v(z) < \mathfrak p^{-1}\}$ one has $f(z) = c \cdot \prod_{t \in T}(z - t)^{m_t} \cdot (1 + h(z))$ with $v(h(z)) < 1$, and moreover $h$ is uniformly small on closed substars: for every $\rho \in \Gamma_0$ with $\mathfrak p < \rho \le 1$ there is $\delta < 1$ with $v(h(z)) \le \delta$ for all $z \in \Omega$ satisfying $v(z - t) \ge \rho$ for all $t \in T$ and $v(z) \le \rho^{-1}$.
--
--   This is the rigid-analytic normal form for a unit of the ring of holomorphic functions on a connected affinoid subdomain of the line, here the standard vertex star of the Drinfeld upper half plane: a nonzero constant times a monomial in the residue parameters $z - t$ times $1 + h$ with $h$ small, the smallness being stated both pointwise on the open star and uniformly on each closed substar. It feeds the computation of the valuations of units along edges and path cycles in the Čerednik–Drinfeld analysis, being cited by [`CerednikDrinfeld.Omega.exists_v_det_eq_one_of_isUnit_det_pathCycle_of_finite`](thm.html#CerednikDrinfeld.Omega.exists_v_det_eq_one_of_isUnit_det_pathCycle_of_finite) and [`CerednikDrinfeld.Omega.v_apply_eq_and_v_apply_eq_mul_zpow_of_isUnit_of_forall_mem_stdEdgeTube`](thm.html#CerednikDrinfeld.Omega.v_apply_eq_and_v_apply_eq_mul_zpow_of_isUnit_of_forall_mem_stdEdgeTube).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_eq_mul_prod_zpow_mul_one_add_of_isUnit.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_eq_mul_prod_zpow_mul_one_add_of_isUnit
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (T : Finset K₀) (hT : ∀ t ∈ T, Valued.v (algebraMap K₀ K t) ≤ 1)
    (hTcov : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < 1)
    (hTsep : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → 1 ≤ Valued.v (algebraMap K₀ K t - algebraMap K₀ K t'))
    (f : ↥(holRing ϖ)) (hf : IsUnit f) :
    ∃ (c : K) (m : K₀ → ℤ) (h : ↥(holRing ϖ)), c ≠ 0 ∧
      (∀ z : ↥(upperHalfPlane K₀ K),
        (∀ t ∈ T, Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v ((z : K) - algebraMap K₀ K t)) →
        Valued.v (z : K) < (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ →
          (f : ↥(upperHalfPlane K₀ K) → K) z =
              c * (∏ t ∈ T, ((z : K) - algebraMap K₀ K t) ^ (m t)) * (1 + (h : ↥(upperHalfPlane K₀ K) → K) z) ∧
          Valued.v ((h : ↥(upperHalfPlane K₀ K) → K) z) < 1) ∧
      ∀ ρ : Γ₀, Valued.v (algebraMap K₀ K ϖ.ϖ) < ρ → ρ ≤ 1 →
        ∃ δ : Γ₀, δ < 1 ∧ ∀ z : ↥(upperHalfPlane K₀ K),
          (∀ t ∈ T, ρ ≤ Valued.v ((z : K) - algebraMap K₀ K t)) → Valued.v (z : K) ≤ ρ⁻¹ →
            Valued.v ((h : ↥(upperHalfPlane K₀ K) → K) z) ≤ δ := by sorry
