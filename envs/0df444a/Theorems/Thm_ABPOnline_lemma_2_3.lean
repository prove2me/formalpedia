-- Prove2me | Theorems.Thm_ABPOnline_lemma_2_3
-- name    : ABPOnline.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:57:15.209183+00:00
-- url     : https://prove2.me/theorems/52fae402-a4a7-440d-8da0-78a3f0b3aba9
-- title:
--   Lemma 2.3 — $\mathbb E(\kappa-Z)_+^2\le E_\star(\kappa)\le(\kappa_++\sqrt8)^2$, hence $0<E_\star(\kappa)<\infty$
-- statement:
--   Let $B$ be a standard Brownian motion on $[0,1]$ and $Z\sim N(0,1)$. For every $\kappa\in\mathbb R$,
--   $$
--   \mathbb E(\kappa-Z)_+^2\le E_\star(\kappa)\le(\kappa_++\sqrt8)^2 .
--   $$
--   In particular $0<E_\star(\kappa)<\infty$.
--
--   These bounds make the right-hand side of Theorem 1.1 a finite positive number and drive the large-margin asymptotics of §5.
--
--   Differences from the source:
--   - generalization: E⋆(κ) defined from a standard Brownian motion B = (B_t)_{0≤t≤1} with its completed natural filtration → the statement holds for every process B with IsBrownianOn1 B P on every probability space, with E⋆ computed on that B; reason: E⋆(κ) depends only on the law of B; the source's Brownian motion is one such process
--   - encoding: E⋆(κ) a real number; E(κ − Z)²₊ and (κ₊ + √8)² → E⋆ in ℝ≥0∞, the two real bounds embedded by ENNReal.ofReal, finiteness as E⋆ < ⊤; reason: the same inequalities; E(κ − Z)²₊ is the Gaussian integral of (max(κ − z, 0))²
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), Lemma 2.3, (8), p.6 (PDF p.7)

import Mathlib
import Definitions.Def_ABPOnline_IsBrownianOn1
import Definitions.Def_ABPOnline_Estar

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ABPOnline

/-- **Lemma 2.3** (arXiv:2609.02124, printed p.6, PDF p.7). For every `κ ∈ ℝ`,
`E(κ − Z)²₊ ≤ E⋆(κ) ≤ (κ₊ + √8)²` with `Z ∼ N(0,1)`; in particular `0 < E⋆(κ) < ∞`.

**Formalization Note** `E⋆` is computed on an arbitrary standard Brownian motion `B` and is in
`ℝ≥0∞`; the Gaussian moment is a real integral, embedded by `ENNReal.ofReal`. -/
theorem lemma_2_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianOn1 B P) (κ : ℝ) :
    ENNReal.ofReal (∫ z, (max (κ - z) 0) ^ 2 ∂(gaussianReal 0 1)) ≤ Estar P B κ ∧
    Estar P B κ ≤ ENNReal.ofReal ((max κ 0 + Real.sqrt 8) ^ 2) ∧
    0 < Estar P B κ ∧ Estar P B κ < ⊤ := by sorry

end ABPOnline
