-- Prove2me | Theorems.Thm_ContinualCounting_eq_13_weighted_sum_to_max
-- name    : ContinualCounting.eq_13_weighted_sum_to_max
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:44:07.936935+00:00
-- url     : https://prove2.me/theorems/9be8e1a3-2bab-4a1a-9f6e-ce1605b99486
-- title:
--   Eq. (13), the claim — from the weighted sum to one large term
-- statement:
--   Let $4\mid h$ (so $n=2^h$ with $h/4$ an integer) and let $z$ be a random noise vector in $\mathbb R^{2^h}$. There is a string $s\in\{\ell,r\}^{h/2}$ (the one fixed after (12)) such that for every $\sigma\in[0,\infty]$: if every selection $\mathcal J\subseteq\{0,\dots,h/2-1\}$ with $|\mathcal J|=h/4$, and $\{J_d\}_{d\in\mathcal J}$ with $J_d$ a set of $2^{d-1}$ of the nodes of $\mathcal T^s$ at depth $2d$ for $d>0$ and $J_0=\{\rho\}$, satisfies $\max_{d\in\mathcal J}\max_{u\in J_d}\sigma_{u,\tilde s_{d+1}}\ge\sigma$, then
--   $$\mathbb E\big[\|z\|_\infty\big]\ge\frac{h\sigma}{32}.$$
--
--   Differences from the source:
--   - reading: "Fix such an s" (the s of (12)), then the claim for that s → ∃ s such that the claim holds for every σ; reason: the claim is made for the s whose existence (12) asserts, and the rest of the proof works for any s
--   - encoding: σ, the residual noises and E[∥z∥∞] real → in ℝ≥0∞ (lintegral of the enorm); reason: Lean convention; same instances, and an infinite expectation only makes the bound easier
-- source:
--   Bairaktari, Dahl, Larsen, The Binary Tree Mechanism is Optimal for Differentially Private Continual Counting, arXiv:2607.00876 (sha256 986e6426…), §5, the claim of eq. (13), pp.23 (PDF p.24)

import Mathlib
import Definitions.Def_ContinualCounting_InTs

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ContinualCounting

/-- **The claim of (13) (from the weighted sum to one large term).** Bairaktari, Dahl, Larsen,
arXiv:2607.00876 (sha256 986e6426…), §5, p.23: "Assume we can show that for any such choice of J and
{J_d}_{d∈J}, we have max_{d∈J} max_{u∈J_d} σ_{u,s̃_{d+1}} ≥ σ, then we claim that E[∥z∥∞] ≥ hσ/32."

**Formalization Note.** `s` is the string fixed after (12) ("Fix such an s"); its existence is stated
here, as in `eq_12_subtree_restriction`. `max_{d∈J} max_{u∈J_d} σ_{u,s̃_{d+1}} ≥ σ` on a finite family is
"some `d ∈ J`, `u ∈ J_d` has `σ ≤ σ_{u,s̃_{d+1}}`", for every admissible selection `J, {J_d}`. `σ`, the
residual noises and `E[∥z∥∞]` are in `ℝ≥0∞`; `∥·∥∞` is the sup norm of `Fin (2^h) → ℝ`. `4 ∣ h` is the
part of §5's assumption "n is a power of 16" that the claim needs (`h/4` is an integer). -/
theorem eq_13_weighted_sum_to_max {h : ℕ} (hh : 4 ∣ h) (ν : Measure (Fin (2 ^ h) → ℝ))
    [IsProbabilityMeasure ν] :
    ∃ s : Fin (h / 2) → Bool, ∀ σ : ℝ≥0∞,
      (∀ (J : Finset ℕ) (Js : ℕ → Finset Node), Admissible h s J Js →
        ∃ d ∈ J, ∃ u ∈ Js d, σ ≤ sigmaTilde ν s u) →
      (h : ℝ≥0∞) * σ / 32 ≤ ∫⁻ z, ‖z‖ₑ ∂ν := by sorry

end ContinualCounting
