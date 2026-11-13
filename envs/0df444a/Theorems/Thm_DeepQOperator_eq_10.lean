-- Prove2me | Theorems.Thm_DeepQOperator_eq_10
-- name    : DeepQOperator.eq_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:03:28.107724+00:00
-- url     : https://prove2.me/theorems/fc5e3389-b361-4ae6-b4c7-78679f886ea0
-- title:
--   (10): randomized fixed exact-affine designs have regret $\ge\gamma(m-N)_+/(256\pi^2m)$
-- statement:
--   Let $m\ge2$ and $0<\gamma<1$. For every randomized fixed design of $N$ arbitrary-affine exact measurements on the family (6),
--   $$\sup_{\theta\in P_{cb}}\mathbb E_\omega\,\ell\big(A(\theta;\omega),\theta\big)\ \ge\ \frac{\gamma(m-N)_+}{256\pi^2m}.\tag{10}$$
--
--   Through the finite-reply simulations of Appendix E.5 this gives both lower bounds of Theorem 2.
--
--   **Formalization Note** $(m-N)_+=\max(0,m-N)$ in $\mathbb R$. Only this display of Theorem 3 is posed; its CountSketch upper bound is not on the path of Theorem 2.
--
--   Differences from the source:
--   - encoding: 𝔥^{…}_B, the infimum over protocols of sup_θ E_ω ℓ → every protocol of the class satisfies bound ≤ ⨆_{θ ∈ P_cb} ∫⁻ ω, ofReal ℓ(A(θ;ω), θ) dμ; reason: an infimum is ≥ a bound iff every member is; the supremum need not be attained
--   - encoding: randomness on a standard Borel space → seed space Ω : Type with [StandardBorelSpace Ω] and a probability measure; the protocol is measurable in the seed, quantizers jointly measurable; reason: §5 p.8; every standard Borel space is Borel isomorphic to a Borel subset of ℝ, so Ω : Type omits none
--   - encoding: "N arbitrary-affine measurements" → an ExactDesign with N rows, zero rows allowed; reason: a zero row is a constant
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Theorem 3, eq. (10), p.5 (PDF p.8); proved in Appendix D.4, p.22

import Mathlib
import Definitions.Def_DeepQOperator_Family
import Definitions.Def_DeepQOperator_ExactDesign
import Definitions.Def_DeepQOperator_ScoreMatrix

open MeasureTheory Matrix

namespace DeepQOperator

/-- **(10)** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), Theorem 3, p.5, PDF p.8; proved in Appendix D.4, p.22).

For every randomized fixed design of `N` arbitrary-affine measurements,
`𝔥^{fixed,aff,ran}_N ≥ γ(m - N)₊/(256π²m)` on the family (6).

**Formalization Note.** `(m - N)₊` is `max 0 (m - N)` in `ℝ`. The seed space is any standard Borel
probability space, the design is measurable and has `N` rows (zero rows allowed), and the regret is the
worst expected loss (3) over `P_cb`. Only this display of Theorem 3 is posed; Theorem 3's upper bound
(11)–(12) is not on the path of Theorem 2.
-/
theorem eq_10 (m : ℕ) (hm : 2 ≤ m) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    (∀ (N : ℕ) (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
        [IsProbabilityMeasure μ] (D : ExactDesign (Coord m) Ω N), D.IsMeasurable →
      ENNReal.ofReal (γ * max 0 ((m : ℝ) - N) / (256 * Real.pi ^ 2 * m)) ≤
        designRegret (Pcb m) (loss m γ) μ D) := by sorry

end DeepQOperator
