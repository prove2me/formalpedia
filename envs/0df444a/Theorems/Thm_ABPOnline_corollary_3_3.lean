-- Prove2me | Theorems.Thm_ABPOnline_corollary_3_3
-- name    : ABPOnline.corollary_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:57:47.958202+00:00
-- url     : https://prove2.me/theorems/b368e896-e549-40bd-8428-70c06408ce4f
-- title:
--   Corollary 3.3 — upper bound $\alpha_{\mathrm{on}}(\kappa)\le 2/(\pi E_\star(\kappa))$
-- statement:
--   Let $B$ be a standard Brownian motion on $[0,1]$. For every $\kappa\in\mathbb R$,
--   $$
--   \alpha_{\mathrm{on}}(\kappa)\le\frac{2}{\pi E_\star(\kappa)} .
--   $$
--
--   This is the impossibility half of Theorem 1.1: no online algorithm succeeds with probability tending to one above the threshold.
--
--   Differences from the source:
--   - generalization: E⋆(κ) defined from a standard Brownian motion B = (B_t)_{0≤t≤1} with its completed natural filtration → the statement holds for every process B with IsBrownianOn1 B P on every probability space, with E⋆ computed on that B; reason: E⋆(κ) depends only on the law of B; the source's Brownian motion is one such process
--   - encoding: α_on(κ) and E⋆(κ) as a supremum and an infimum of reals, with 2/(πE⋆(κ)) → values in ℝ≥0∞ and the identity in ℝ≥0∞; reason: no junk value for an empty or unbounded set; by Lemma 2.3, 0 < E⋆(κ) < ∞, so the identity is the real one
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), Corollary 3.3, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_ABPOnline_IsBrownianOn1
import Definitions.Def_ABPOnline_alphaOn
import Definitions.Def_ABPOnline_Estar

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ABPOnline

/-- **Corollary 3.3** (arXiv:2609.02124, printed p.10, PDF p.11). For every `κ ∈ ℝ`,
`α_on(κ) ≤ 2/(πE⋆(κ))`.

**Formalization Note** In `ℝ≥0∞`; `E⋆` is computed on an arbitrary standard Brownian motion. -/
theorem corollary_3_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianOn1 B P) (κ : ℝ) :
    alphaOn κ ≤ 2 / (ENNReal.ofReal Real.pi * Estar P B κ) := by sorry

end ABPOnline
