-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_RatPair_v_evalAt_sub_evalAt_le_mul_of_isPoleFreeOn_affinoid
-- name    : CerednikDrinfeld.Omega.RatPair.v_evalAt_sub_evalAt_le_mul_of_isPoleFreeOn_affinoid
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/f3cb97ee-299b-550d-8b58-a4ee8e9e6621
-- title:
--   Oscillation bound for rational functions bounded on a Drinfeld affinoid
-- statement:
--   Let $K_0$ be a field and $K$ an algebraically closed field which is a $K_0$-algebra and carries a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$. Let $\varpi$ be a pseudo-uniformiser of $K_0$ relative to $K$, i.e. an element $\varpi \in K_0$ with $0 < v(\varpi) < 1$ in $K$ such that every nonzero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N \in \mathbb{N}$; write $\mathfrak{p} = v(\varpi)$ (image in $K$). Fix naturals $n \le m$, and assume the finiteness hypothesis that there is a finite set $T \subseteq K_0$ with the property that every $a \in K_0$ with $v(a) \le \mathfrak{p}^{-m}$ satisfies $v(a - t) < \mathfrak{p}^{m}$ for some $t \in T$. For $k \in \mathbb{N}$ let the level-$k$ affinoid be the set of $z \in K$ with $v(z) \le \mathfrak{p}^{-k}$ and $\mathfrak{p}^{k} \le v(z - a)$ for every $a \in K_0$ with $v(a) \le \mathfrak{p}^{-k}$. Let $r$ be a pair of polynomials $(\mathrm{num}, \mathrm{den})$ over $K$, with evaluation $r(z) = \mathrm{num}(z)/\mathrm{den}(z)$, such that $\mathrm{den}$ has no zero on the level-$m$ affinoid, and let $b \in K$ be such that $v(r(w)) \le v(b)$ for all $w$ in the level-$m$ affinoid. Then for all $z, z_0$ in the level-$n$ affinoid, $v(r(z) - r(z_0)) \le \mathfrak{p}^{\,m-n} \, v(b)$.
--
--   This is the rational-function core of Liouville's theorem for Drinfeld's upper half plane: a function bounded by $b$ on the level-$m$ member of the affinoid exhaustion varies by at most $|\varpi|^{m-n}|b|$ on the level-$n$ member, so that letting $m \to \infty$ forces constancy. It is used in [`CerednikDrinfeld.Omega.exists_eq_algebraMap_of_forall_v_apply_le`](thm.html#CerednikDrinfeld.Omega.exists_eq_algebraMap_of_forall_v_apply_le), where the bound is applied to rational approximants of a bounded rigid-holomorphic function at every level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_RatPair_v_evalAt_sub_evalAt_le_mul_of_isPoleFreeOn_affinoid.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.RatPair.v_evalAt_sub_evalAt_le_mul_of_isPoleFreeOn_affinoid
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K) (n m : ℕ) (hnm : n ≤ m)
    (hfin : ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ m)
    (r : RatPair K) (hr : r.IsPoleFreeOn (affinoid ϖ m))
    (b : K) (hb : ∀ w : K, w ∈ affinoid ϖ m → Valued.v (r.evalAt w) ≤ Valued.v b)
    {z z₀ : K} (hz : z ∈ affinoid ϖ n) (hz₀ : z₀ ∈ affinoid ϖ n) :
    Valued.v (r.evalAt z - r.evalAt z₀) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (m - n) * Valued.v b := by sorry
