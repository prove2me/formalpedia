-- Prove2me | Theorems.Thm_AlmostMMS_Supplement_theorem_2_2
-- name    : AlmostMMS.Supplement.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:29:50.409261+00:00
-- url     : https://prove2.me/theorems/93257efb-773e-4b7c-82d3-40e2b3d301cb
-- title:
--   Theorem 2.2 — head rounding with loss $\rho(h,X)$
-- statement:
--   Let $n$ agents have nonnegative item values $v_i(e)$ on items $e_1,\dots,e_m$, and let $h\ge1$ be an integer. Let $\Pi$ be a shared set of head profiles for head size $h$ (containing $\varnothing$ and $\bot$) such that $|\pi|\le h$ for every $\pi\in\Pi-\bot$. For every agent $i$ let $(x_i,\Pi)$ be a fractional profile: $x_i(\pi)\ge0$ and $\sum_{\pi\in\Pi}x_i(\pi)=1$. Write $X=|\{(i,\pi):0<x_i(\pi)<1\}|$.
--
--   Then there are integral profiles $y=\{y_i\}_{i\in N}$ over $\Pi$ such that
--
--   1. $y_i(\pi)\in\{0,1\}$ for all $i,\pi$, and $\sum_{\pi\in\Pi}y_i(\pi)=1$;
--   2. $y_i(\pi)=1$ for $\pi\ne\bot$ only if $x_i(\pi)>0$;
--   3. $\mathcal H(y,\Pi,\ell)\le\mathcal H(x,\Pi,\ell)$ for every $0\le\ell\le m$;
--   4. $\tau(y,\Pi)\le\tau(x,\Pi)$;
--   5. $\mathcal I(y,\Pi)\le\mathcal I(x,\Pi)$ and
--   $$
--   \mathcal I(y,\Pi)\ \ge\ \mathcal I(x,\Pi)-\rho(h,X),\qquad \rho(h,X)=8+4\log_2X\,(1+\ln h+\ln X).
--   $$
--
--   Here $\mathcal H(x,\Pi,\ell)=\sum_i\sum_{\pi}x_i(\pi)P_i(\pi,\ell)$ is the total prefix head load ($P_i(\pi,\ell)$ counts the demands of $\pi$ that only the first $\ell$ items can satisfy for agent $i$), $\tau$ is the total tail load with the §2 deficit $(1-v(\pi))_+$, and $\mathcal I(x,\Pi)=\sum_i\sum_{\pi\ne\bot}x_i(\pi)$ is the fractional number of selected agents. This rounding loses only $O(\log^2 n)$ agents in the proof of Theorem 2.1.
--
--   Differences from the source:
--   - generalization: §2's standing Assumption 1 (item values in [0, 1], non-increasing in a common order, MMS bundles of value 1) → item values only nonnegative; reason: the proof (pp.47–50) uses only prefix loads, breakpoints and τ ≥ 0, and the source's instances satisfy the weaker hypothesis
--   - generalization: demands in (0, 1] (Definition 2.1) → positive demands, each profile's demands equal to head values v_i(e) of one agent; reason: the upper bound 1 comes only from Assumption 1's v_i(e) ≤ 1, which the proof does not use
--   - generalization: head size h ∈ [m] (Definition 2.6) → any integer h ≥ 1 (the theorem's own hypothesis); reason: for h ≥ m there is no tail and every T_i = 0, a case the proof covers unchanged; h ∈ [m] specializes it
--   - encoding: ⊥, ∅, profiles and integral profiles → none, some 0, Multiset ℝ, and y of the same type as x read on Π; reason: Lean representation, same instances
--   - encoding: log X and ln X at X = 0 → Real.logb 2 0 = Real.log 0 = 0, so ρ(h, 0) = 8; reason: the printed formula is undefined at X = 0, where x is already integral
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Theorem 2.2, p.18 (= Theorem A.1, p.47)

import Mathlib
import Definitions.Def_AlmostMMS_fracH
import Definitions.Def_AlmostMMS_Supplement_fracTauH
import Definitions.Def_AlmostMMS_Supplement_IsHeadProfileSetH
import Definitions.Def_AlmostMMS_Supplement_rhoHead

namespace AlmostMMS.Supplement

open Finset AlmostMMS

/-- **Theorem 2.2 (Head rounding), p.18 (= Theorem A.1, p.47).** Feige, Grinberg, *Almost-MMS
allocations with small agent redundancy*, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256
3925c4ab…): let `Π` be a shared set of head profiles with `|π| ≤ h` for an integer `h ≥ 1`, and let
`(x_i, Π)` be fractional profiles. There are integer head profiles `(y_i, Π)` with `y_i(π) ∈ {0, 1}`,
`y_i(π) = 1` for `π ≠ ⊥` only if `x_i(π) > 0`, and `H(y, Π, ℓ) ≤ H(x, Π, ℓ)` for all `0 ≤ ℓ ≤ m`,
`τ(y, Π) ≤ τ(x, Π)`, `I(y, Π) ≤ I(x, Π)` and `I(y, Π) ≥ I(x, Π) - ρ(h, X)`, where
`X = |{(i, π) : 0 < x_i(π) < 1}|` and `ρ(h, X) = 8 + 4 log X · (1 + ln h + ln X)`.

**Formalization Note.** `H`, `I`, `X` and fractional profiles are the published `AlmostMMS.fracH`,
`fracI`, `fracX`, `IsFractionalProfile` (none depends on `q`); `τ` is the §2 total tail load
`fracTauH` with the common head size `h` and the §2 deficit `(1 - v(π))₊`. The same `h` bounds the
profile sizes and defines head and tail items, as in the proof of Theorem 2.1. The valuation only has
to be nonnegative: the proof (pp.47–50) uses neither the common item order nor the MMS bundles.
`y` has the same type as `x`, read on `Π`. -/
theorem theorem_2_2 {n m h : ℕ} (hh : 1 ≤ h) (v : Fin n → Fin m → ℝ) (hv : ∀ i e, 0 ≤ v i e)
    (Ps : Finset (Option (Multiset ℝ))) (hPs : IsHeadProfileSetH v h Ps)
    (hcard : ∀ p, some p ∈ Ps → p.card ≤ h)
    (x : Fin n → Option (Multiset ℝ) → ℝ) (hx : IsFractionalProfile Ps x) :
    ∃ y : Fin n → Option (Multiset ℝ) → ℝ, IsFractionalProfile Ps y ∧
      (∀ i, ∀ π ∈ Ps, y i π = 0 ∨ y i π = 1) ∧
      (∀ i p, some p ∈ Ps → y i (some p) = 1 → 0 < x i (some p)) ∧
      (∀ ℓ ≤ m, fracH v Ps y ℓ ≤ fracH v Ps x ℓ) ∧
      fracTauH v h Ps y ≤ fracTauH v h Ps x ∧
      fracI Ps y ≤ fracI Ps x ∧
      fracI Ps x - rhoHead h (fracX Ps x) ≤ fracI Ps y := by sorry

end AlmostMMS.Supplement
