-- Prove2me | Theorems.Thm_ABPOnline_lemma_2_5
-- name    : ABPOnline.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:54:32.107288+00:00
-- url     : https://prove2.me/theorems/0d051911-e220-4d6a-8b24-d16e3e64685f
-- title:
--   Lemma 2.5 — every drift in the ball $\|b\|_2\le c_G/\sqrt N$ is realized by a sign, with a fresh Gaussian innovation
-- statement:
--   Let $Z\sim N(0,I_M/N)$ be independent of a $\sigma$-field $\mathcal H$, and let $b\in\mathbb R^M$ be $\mathcal H$-measurable with $\|b\|_2\le c_G/\sqrt N$. Then there are an $\mathcal H\vee\sigma(Z)$-measurable sign $\varepsilon\in\{-1,+1\}$ and a random vector $\Delta B$ such that
--   $$
--   \mathbb E[\varepsilon Z\mid\mathcal H]=b,\qquad \Delta B\sim N(0,I_M/N),
--   $$
--   with $\Delta B$ independent of $\mathcal H$. Moreover, given $\mathcal H$, the map $Z\mapsto(\varepsilon,\Delta B)$ is invertible: $(\varepsilon,\Delta B)=F(b,Z)$ for a measurable map $F$, and $F(c,\cdot)$ has a measurable left inverse for every admissible drift $c$.
--
--   This is the converse of Lemma 2.4 and the basis of the steering step of Algorithm 1.
--
--   Differences from the source:
--   - encoding: a sigma-field H, Z ∼ N(0, I_M/N) → H a sub-σ-algebra of the ambient one; Z measurable with law the product of M Gaussians of variance 1/N; conditional expectations coordinatewise; reason: the standard meaning of the objects
--   - encoding: ‖b‖₂ ≤ c_G/√N → the bound at every sample point; reason: the source states it for the random vector b
--   - reading: "given H, the map Z ↦ (ε, ∆B) is invertible" → (ε, ∆B) = F(b, Z) for a measurable F, and F(c, ·) has a measurable left inverse for every c with ‖c‖₂ ≤ c_G/√N; reason: the H-information enters through b, as in the construction (10)–(11) and its inverse in the proof
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), Lemma 2.5, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_ABPOnline_cG

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ABPOnline

/-- **Lemma 2.5** (arXiv:2609.02124, printed p.7, PDF p.8). Let `Z ∼ N(0, I_M/N)` be independent of
a σ-field `H`, and let `b ∈ ℝ^M` be `H`-measurable with `‖b‖₂ ≤ c_G/√N`. Then there are an
`H ∨ σ(Z)`-measurable sign `ε ∈ {−1,+1}` and a random vector `∆B` such that `E[εZ | H] = b`,
`∆B ∼ N(0, I_M/N)`, with `∆B` independent of `H`. Moreover, given `H`, the map `Z ↦ (ε, ∆B)` is
invertible.

**Formalization Note** "Given `H`, the map is invertible" is read as: `(ε, ∆B) = F(b, Z)` for a
measurable map `F`, and `F(c, ·)` has a measurable left inverse `F⁻¹(c, ·)` for every admissible
drift `c` (`‖c‖₂ ≤ c_G/√N`); the `H`-information enters through `b`, as in the construction
(10)–(11). -/
theorem lemma_2_5 {Ω : Type*} (H : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hH : H ≤ mΩ) {M N : ℕ} (Z : Ω → Fin M → ℝ) (hZm : Measurable Z)
    (hZ : P.map Z = Measure.pi fun _ : Fin M => gaussianReal 0 (N : ℝ≥0)⁻¹)
    (hind : Indep H (MeasurableSpace.comap Z inferInstance) P) (b : Ω → Fin M → ℝ)
    (hbm : Measurable[H] b) (hb : ∀ ω, l2norm (b ω) ≤ cG / Real.sqrt N) :
    ∃ ε : Ω → ℝ, ∃ ΔB : Ω → Fin M → ℝ,
      (∀ ω, ε ω = 1 ∨ ε ω = -1) ∧
      Measurable[H ⊔ MeasurableSpace.comap Z inferInstance] ε ∧
      (∀ i : Fin M, P[fun ω => ε ω * Z ω i | H] =ᵐ[P] fun ω => b ω i) ∧
      Measurable ΔB ∧
      P.map ΔB = (Measure.pi fun _ : Fin M => gaussianReal 0 (N : ℝ≥0)⁻¹) ∧
      Indep H (MeasurableSpace.comap ΔB inferInstance) P ∧
      ∃ F : (Fin M → ℝ) → (Fin M → ℝ) → ℝ × (Fin M → ℝ), Measurable (Function.uncurry F) ∧
        (∀ ω, (ε ω, ΔB ω) = F (b ω) (Z ω)) ∧
        ∃ Finv : (Fin M → ℝ) → ℝ × (Fin M → ℝ) → (Fin M → ℝ),
          Measurable (Function.uncurry Finv) ∧
          ∀ c z : Fin M → ℝ, l2norm c ≤ cG / Real.sqrt N → Finv c (F c z) = z := by sorry

end ABPOnline
