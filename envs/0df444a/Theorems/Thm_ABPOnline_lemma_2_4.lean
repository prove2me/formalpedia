-- Prove2me | Theorems.Thm_ABPOnline_lemma_2_4
-- name    : ABPOnline.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:54:23.940719+00:00
-- url     : https://prove2.me/theorems/32911254-d106-46fe-995b-cdee86241bac
-- title:
--   Lemma 2.4 — one-column drift bound $\|\mathbb E[\varepsilon Z\mid\mathcal H]\|_2\le c_G/\sqrt N$
-- statement:
--   Let $Z\sim N(0,I_M/N)$ be independent of a $\sigma$-field $\mathcal H$, and let $\varepsilon\in\{-1,+1\}$ be measurable with respect to $\mathcal H\vee\sigma(Z)$. Then
--   $$
--   b:=\mathbb E[\varepsilon Z\mid\mathcal H]\quad\text{satisfies}\quad \|b\|_2\le\frac{c_G}{\sqrt N}\quad\text{a.s.}
--   $$
--
--   Every conditional drift of one signed Gaussian column lies in the Euclidean ball of radius $c_G/\sqrt N$; this is the constraint behind the upper bound on $\alpha_{\mathrm{on}}$.
--
--   Differences from the source:
--   - encoding: a sigma-field H, Z ∼ N(0, I_M/N) → H a sub-σ-algebra of the ambient one; Z measurable with law the product of M Gaussians of variance 1/N; conditional expectations coordinatewise; reason: the standard meaning of the objects
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), Lemma 2.4, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_ABPOnline_cG

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ABPOnline

/-- **Lemma 2.4** (arXiv:2609.02124, printed p.7, PDF p.8). Let `Z ∼ N(0, I_M/N)` be independent of
a σ-field `H`, and let `ε ∈ {−1,+1}` be `H ∨ σ(Z)`-measurable. Then `b := E[εZ | H]` satisfies
`‖b‖₂ ≤ c_G/√N` almost surely.

**Formalization Note** `H` is a sub-σ-algebra of the ambient one; the vector conditional
expectation is taken coordinatewise. `N(0, I_M/N)` is the product of `M` centred Gaussians of
variance `1/N`. -/
theorem lemma_2_4 {Ω : Type*} (H : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hH : H ≤ mΩ) {M N : ℕ} (Z : Ω → Fin M → ℝ) (hZm : Measurable Z)
    (hZ : P.map Z = Measure.pi fun _ : Fin M => gaussianReal 0 (N : ℝ≥0)⁻¹)
    (hind : Indep H (MeasurableSpace.comap Z inferInstance) P) (ε : Ω → ℝ)
    (hε : ∀ ω, ε ω = 1 ∨ ε ω = -1)
    (hεm : Measurable[H ⊔ MeasurableSpace.comap Z inferInstance] ε) :
    ∀ᵐ ω ∂P, l2norm (fun i => (P[fun ω' => ε ω' * Z ω' i | H]) ω) ≤ cG / Real.sqrt N := by sorry

end ABPOnline
