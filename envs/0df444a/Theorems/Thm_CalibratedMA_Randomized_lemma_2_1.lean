-- Prove2me | Theorems.Thm_CalibratedMA_Randomized_lemma_2_1
-- name    : CalibratedMA.Randomized.lemma_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T21:23:48.22905+00:00
-- url     : https://prove2.me/theorems/b88dc169-632e-43fe-aa2d-98582229a474
-- title:
--   Lemma 2.1 — residual decomposition under postprocessing
-- statement:
--   Let $(X,Y,S)$ be jointly distributed with $Y\in[0,1]$ and $S\in[0,1]$. For each input-score pair $(x,s)$ let $R_{x,s}$ be a distribution on $[0,1]$, and draw the postprocessed prediction $P\sim R_{X,S}$ using randomness independent of $Y$ conditionally on $(X,S)$. For a bounded test $\phi:\mathcal X\times[0,1]\to[-1,1]$ define its lift to the intermediate score by $\phi^\uparrow(x,s)=\mathbb E_{P\sim R_{x,s}}[\phi(x,P)]$. Then
--   $$\mathbb E[\phi(X,P)(Y-P)]=\mathbb E[\phi^\uparrow(X,S)(Y-S)]+\mathbb E[\phi(X,P)(S-P)].\tag{3}$$
--
--   The first term is controlled while the score is learned and the second is the error introduced by coarsening; both upper bounds in the paper rest on this split.
--
--   **Formalization Note.** $\mu$ is the law of $(X,Y,S)$ on $\mathcal X\times\mathbb R\times\mathbb R$, $R$ is a Markov kernel from $\mathcal X\times\mathbb R$ to $\mathbb R$ with $R_{x,s}([0,1]^c)=0$, and the law of $((X,Y,S),P)$ is $\mu\otimes R_{X,S}$ (`Measure.compProd` with the kernel composed with $(x,y,s)\mapsto(x,s)$). This is the formal content of "independent of $Y$ conditionally on $(X,S)$".
--
--   Differences from the source:
--   - reading: "$(X,Y,S)$ jointly distributed" → in addition $Y\in[0,1]$ almost surely; reason: Section 2 fixes $Y\in[0,1]$ for the whole paper; this standing assumption also makes every expectation in (3) finite.
--   - encoding: the family $(R_{x,s})$ of distributions on $[0,1]$ → a Markov kernel (measurable in $(x,s)$) carried by $[0,1]$; reason: measurability is needed for $P\sim R_{X,S}$ to have a joint law.
--   - encoding: bounded test $\phi$ → $\phi$ jointly measurable with values in $[-1,1]$ on $\mathcal X\times[0,1]$; reason: measurability only excludes tests whose expectations are undefined.
-- source:
--   Jiuyao Lu, Georgy Noarov, Aaron Roth, Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity, STOC 2027 submission #900 (October 2026), p. 12, Lemma 2.1, Eq. (3)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace CalibratedMA.Randomized

/-- Lemma 2.1 (p. 12), residual decomposition under postprocessing. `μ` is the joint law of
`(X, Y, S)` (points `(x, y, s)`), `R` the postprocessing kernel `(x, s) ↦ R_{x,s}`, and the joint
law of `((X, Y, S), P)` is `μ ⊗ R_{X,S}`: given `(X, S)`, `P` is drawn independently of `Y`. -/
theorem lemma_2_1 {X : Type*} [MeasurableSpace X] (μ : Measure (X × ℝ × ℝ))
    [IsProbabilityMeasure μ] (hY : ∀ᵐ w ∂μ, w.2.1 ∈ Set.Icc (0 : ℝ) 1)
    (hS : ∀ᵐ w ∂μ, w.2.2 ∈ Set.Icc (0 : ℝ) 1)
    (R : Kernel (X × ℝ) ℝ) [IsMarkovKernel R] (hR : ∀ xs, R xs (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (φ : X → ℝ → ℝ) (hφm : Measurable (Function.uncurry φ))
    (hφ : ∀ x, ∀ p ∈ Set.Icc (0 : ℝ) 1, φ x p ∈ Set.Icc (-1 : ℝ) 1) :
    let ν : Measure ((X × ℝ × ℝ) × ℝ) :=
      μ ⊗ₘ (R.comap (fun w : X × ℝ × ℝ => (w.1, w.2.2)) (by fun_prop))
    let φup : X → ℝ → ℝ := fun x s => ∫ p, φ x p ∂(R (x, s))
    ∫ v, φ v.1.1 v.2 * (v.1.2.1 - v.2) ∂ν =
      ∫ w, φup w.1 w.2.2 * (w.2.1 - w.2.2) ∂μ + ∫ v, φ v.1.1 v.2 * (v.1.2.2 - v.2) ∂ν := by sorry

end CalibratedMA.Randomized
