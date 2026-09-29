-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_affinoid_nonempty_of_exists_finset_cover
-- name    : CerednikDrinfeld.Omega.affinoid_nonempty_of_exists_finset_cover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/42da0227-24dd-5010-a389-6c40a8fb7417
-- title:
--   Nonemptiness of finitely punctured affinoids over algebraically closed K
-- statement:
--   Let $K_0$ be a field and $K$ an algebraically closed field which is a $K_0$-algebra and carries a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$. Let $\varpi$ be a pseudo-uniformiser of $K_0$ relative to $K$, that is, an element $\varpi.\varpi \in K_0$ whose image in $K$ satisfies $0 < v(\varpi) < 1$ and such that every nonzero $a \in K_0$ admits $N \in \mathbb{N}$ with $v(\varpi)^N \le v(a) \le (v(\varpi)^{-1})^N$; write $p = v(\varpi)$ for the value of its image in $K$. Let $n$ be a natural number and assume there is a finite subset $T \subseteq K_0$ such that every $a \in K_0$ whose image in $K$ satisfies $v(a) \le (p^{-1})^{n}$ admits $t \in T$ with $v(a - t) < p^{n}$ (values taken of the images in $K$). The conclusion is that the set $\mathrm{affinoid}\ \varpi\ n$ is nonempty, i.e. there exists $z \in K$ with $v(z) \le (p^{-1})^{n}$ and $p^{n} \le v(z - a)$ for every $a \in K_0$ with $v(a) \le (p^{-1})^{n}$.
--
--   This is the nonemptiness of the $n$-th affinoid exhausting Drinfeld's $p$-adic upper half-plane, under the hypothesis that the relevant $K_0$-points are covered by finitely many discs of radius $p^n$. It is used, at $n = 0$ and in general, for the nonvanishing statements about holomorphic functions and theta products on the half-plane, such as [`CerednikDrinfeld.Omega.eq_zero_of_forall_finite_forall_apply_eq_zero`](thm.html#CerednikDrinfeld.Omega.eq_zero_of_forall_finite_forall_apply_eq_zero) and the period computations in [`AlgebraicCurve.Pic0`](def/AlgebraicCurve_DivisorClassGroup.html#L223).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_affinoid_nonempty_of_exists_finset_cover.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.affinoid_nonempty_of_exists_finset_cover
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K) (n : ℕ)
    (hfin : ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n) :
    (affinoid ϖ n).Nonempty := by sorry
