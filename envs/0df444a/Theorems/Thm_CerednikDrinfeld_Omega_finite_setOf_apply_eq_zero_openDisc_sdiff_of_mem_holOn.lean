-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_openDisc_sdiff_of_mem_holOn
-- name    : CerednikDrinfeld.Omega.finite_setOf_apply_eq_zero_openDisc_sdiff_of_mem_holOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/4f72f535-c6c7-5c9f-91ff-5be27104a998
-- title:
--   Finiteness of zeros in a disc minus finitely many discs
-- statement:
--   Let $K$ be a field carrying a valuation $v$ with values in a linearly ordered commutative group with zero, complete and algebraically closed, let $S\subseteq K$ and let $f\colon S\to K$ lie in the subring $\mathrm{holOn}\,K\,S$, i.e. there is a sequence of rational pairs $r_k$ over $K$, each pole-free on $S$, whose evaluations on $S$ are bounded in valuation by a single $b\in K$ uniformly in $k$ and converge uniformly on $S$ to $f$. Let $c,R\in K$ with $R\neq0$, let $H$ be a finite subset of $K$ and $\rho\colon K\to K$ a function with $\rho(h)\neq0$ and $v(h-c)<v(R)$ for all $h\in H$, and with $v(\rho(h))<v(h-h')$ for distinct $h,h'\in H$; let $E$ be a finite subset of $K$. Assume: every $z$ with $v(z-c)<v(R)$ and $v(\rho(h))<v(z-h)$ for all $h\in H$ lies in $S$; every $z$ with $v(z-c)=v(R)$ and $v(R)\le v(z-e)$ for all $e\in E$ lies in $S$; for each $h\in H$, every $z$ with $v(z-h)=v(\rho(h))$ and $v(\rho(h))\le v(z-e)$ for all $e\in E$ lies in $S$; and $f$ is non-zero at some point of $S$ on the outer circle $v(z-c)=v(R)$ subject to $v(R)\le v(z-e)$ for all $e\in E$, and likewise at some such point of each inner circle $v(z-h)=v(\rho(h))$ subject to $v(\rho(h))\le v(z-e)$ for all $e\in E$. Then the set of $z\in S$ with $v(z-c)<v(R)$, $v(\rho(h))<v(z-h)$ for all $h\in H$, and $f(z)=0$ is finite.
--
--   This is the non-archimedean finiteness-of-zeros statement for a function holomorphic in the sense of uniform approximation by pole-free rational functions, on an open disc with finitely many closed discs removed, under the assumption that $f$ does not vanish identically on any of the bounding circles. It is used in the proof of finiteness of the zero set of such a function on an affinoid, in the analytic groundwork for the Čerednik–Drinfeld description of $p$-adic uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_openDisc_sdiff_of_mem_holOn.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.finite_setOf_apply_eq_zero_openDisc_sdiff_of_mem_holOn
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    [CompleteSpace K] [IsAlgClosed K]
    {S : Set K} {f : ↥S → K} (hf : f ∈ holOn K S)
    (c R : K) (hR : R ≠ 0)
    (H : Finset K) (ρ : K → K) (hρ : ∀ h ∈ H, ρ h ≠ 0)
    (hHc : ∀ h ∈ H, Valued.v (h - c) < Valued.v R)
    (hdisj : ∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → Valued.v (ρ h) < Valued.v (h - h'))
    (E : Finset K)
    (hU : ∀ z : K, Valued.v (z - c) < Valued.v R → (∀ h ∈ H, Valued.v (ρ h) < Valued.v (z - h)) → z ∈ S)
    (hout : ∀ z : K, Valued.v (z - c) = Valued.v R → (∀ e ∈ E, Valued.v R ≤ Valued.v (z - e)) → z ∈ S)
    (hin : ∀ h ∈ H, ∀ z : K, Valued.v (z - h) = Valued.v (ρ h) →
      (∀ e ∈ E, Valued.v (ρ h) ≤ Valued.v (z - e)) → z ∈ S)
    (hout₀ : ∃ z : ↥S, Valued.v ((z : K) - c) = Valued.v R ∧
      (∀ e ∈ E, Valued.v R ≤ Valued.v ((z : K) - e)) ∧ f z ≠ 0)
    (hin₀ : ∀ h ∈ H, ∃ z : ↥S, Valued.v ((z : K) - h) = Valued.v (ρ h) ∧
      (∀ e ∈ E, Valued.v (ρ h) ≤ Valued.v ((z : K) - e)) ∧ f z ≠ 0) :
    {z : ↥S | Valued.v ((z : K) - c) < Valued.v R ∧
      (∀ h ∈ H, Valued.v (ρ h) < Valued.v ((z : K) - h)) ∧ f z = 0}.Finite := by sorry
