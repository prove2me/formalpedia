-- Prove2me | Theorems.Thm_AdaptiveProtection_Convergence_lemma3_bounded
-- name    : AdaptiveProtection.Convergence.lemma3_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:16.311448+00:00
-- url     : https://prove2.me/theorems/27b9b4a0-c56a-4df1-a45c-63d0eaa0125a
-- title:
--   Lemma 3, p. 764 — with bounded demands, the iterates θ^n stay bounded (a.s.)
-- statement:
--   Let fares satisfy $f_1 > f_2 > \cdots > f_{k+1} > 0$ and let the class demands $X_1, \dots, X_{k+1}$ be independent, nonnegative and bounded by a constant $C$ almost surely. Let $(\gamma_n)_{n \ge 1}$ be nonnegative and nonincreasing, and let $\theta^n$ follow the recursion (4) from an arbitrary initial vector $\theta^1$, driven by independent flights with this demand law. Then there is a constant $M$ such that, almost surely,
--   $$|\theta^n_i| \le M \qquad \text{for all } n \ge 1 \text{ and } i = 1, \dots, k.$$
--
--   This boundedness is used throughout the proof of Theorem 1: it makes the errors $T_n = \theta^n_{i+1} - \theta^*_{i+1}$ uniformly bounded and lets assumption A2 be applied on a bounded window.
--
--   **Formalization Note** The paper's "$|\theta^n|$ is bounded (a.s.)" is read as a bound $M$ that is uniform in $n$ and in the sample path, which is how the proof uses it ("$|T_n| \le C$ (a.s.)"). The standing assumptions of §1 that the argument needs are added: nonnegative demands, and strictly decreasing positive fares (so that $r_{i+1} \ge r_{i+2}$). The step sequence is nonincreasing from $\gamma_1$ on, so that $\gamma_n = A/(n+B)$ qualifies; Lean's `γ 0` is never read.
-- source:
--   van Ryzin & McGill, Management Science 46(6), 2000, p. 764, Lemma 3

import Mathlib
import Definitions.Def_NestedSeatAlloc_ProbCond_Model
import Definitions.Def_AdaptiveProtection_Convergence_Setting

open MeasureTheory Filter Topology

namespace AdaptiveProtection.Convergence

/-- Lemma 3 (p. 764): if every class's demand is bounded by `C` (a.s.), the iterates of (4) stay
in a bounded set (a.s.), uniformly in `n`. Stated for any nonnegative step sequence that is
nonincreasing from `γ 1` on. -/
theorem lemma3_bounded
    (k : ℕ) (f : ℕ → ℝ) (hf : ∀ i, 1 ≤ i → i ≤ k → f (i + 1) < f i) (hfpos : 0 < f (k + 1))
    (ν : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hnonneg : ∀ i, 1 ≤ i → i ≤ k + 1 → ∀ᵐ t ∂(ν i), 0 ≤ t)
    (Cb : ℝ) (hbd : ∀ i, 1 ≤ i → i ≤ k + 1 → ∀ᵐ t ∂(ν i), t ≤ Cb)
    (γ : ℕ → ℝ) (hγ0 : ∀ n, 0 ≤ γ n) (hγanti : ∀ n, 1 ≤ n → γ (n + 1) ≤ γ n)
    (θ₁ : ℕ → ℝ) :
    ∃ M : ℝ, ∀ᵐ ω ∂(pathLaw ν), ∀ n i, 1 ≤ i → i ≤ k → |iterate f k γ θ₁ ω n i| ≤ M := by sorry

end AdaptiveProtection.Convergence
