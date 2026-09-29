-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_isDomain_holRing
-- name    : CerednikDrinfeld.Omega.isDomain_holRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/19a4f1ae-f9ee-5c89-83a3-13ff382d7d18
-- title:
--   The ring of holomorphic functions on Ω is a domain
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra which is a field, equipped with a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, and assume $K$ is complete and algebraically closed. Let $\varpi$ be a pseudo-uniformizer of $K_0$ in $K$, i.e. an element $\varpi \in K_0$ with $0 < v(\varpi) < 1$ in $K$ and such that every nonzero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N \in \mathbb{N}$. Three hypotheses are imposed: ($h_{rk}$) for all $x, y \in K$ with $v(x) < 1$ and $y \ne 0$ there is $n$ with $v(x)^n \le v(y)$; ($h_{ex}$) `IsExhausted`, i.e. every $z \in K$ outside the image of $K_0$ lies in the affinoid $\Omega_n = \{z : v(z) \le v(\varpi)^{-n}$ and $v(\varpi)^n \le v(z - a)$ for all $a \in K_0$ with $v(a) \le v(\varpi)^{-n}\}$ for some $n$; ($h_{fin}$) for each $n$ there is a finite subset $T \subseteq K_0$ such that every $a \in K_0$ with $v(a) \le v(\varpi)^{-n}$ satisfies $v(a - t) < v(\varpi)^n$ for some $t \in T$. The conclusion is that the subring `holRing ϖ` of functions $\Omega = K \setminus K_0 \to K$ consisting of those $f$ whose restriction to each $\Omega_n$ is a uniform limit of a uniformly bounded sequence of rational functions without poles on $\Omega_n$ is an integral domain: it is nontrivial and has no zero divisors.
--
--   This is the identity principle for rigid-analytic functions on Drinfeld's $p$-adic upper half plane, in the form that the ring of such functions has no zero divisors (so that its fraction field is available). It is used in the construction of theta functions and of the order-of-vanishing invariants attached to the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_isDomain_holRing.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.isDomain_holRing
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n) :
    IsDomain ↥(holRing ϖ) := by sorry
