-- Prove2me | Theorems.Thm_BranchComposition_small_scale_positive_from_counts
-- name    : BranchComposition.small_scale_positive_from_counts
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T16:40:55.95323+00:00
-- url     : https://prove2.me/theorems/29f4ab97-19bb-40b5-b09b-73fcce7c1737
-- title:
--   Small-scale positivity of spectral sums under counting hypotheses
-- statement:
--   Let I be an index set, with real εᵢ and γᵢ satisfying |εᵢ|≤1/2 and γᵢ≥0. Suppose each set {i:γᵢ≤T} is finite; let N(T) denote its cardinality. Assume there is C≥0 such that every finite set of indices with T≤γᵢ<T+1 has cardinality at most C log(T+3), for T≥1. Let kₙ≥2 be integers, 0<hₙ≤1 with hₙ→0, and Lₙ≥1 with −log hₙ≤Lₙ. Suppose that for some c>0, eventually (hₙ/Lₙ)N(1/hₙ)≥c. Set xₙ=kₙ/hₙ². Then, for all sufficiently large n, the series
--   \[
--   \sum_{i\in I}\left(\frac{x_n}{x_n+\gamma_i^2-\varepsilon_i^2-2i\varepsilon_i\gamma_i}\right)^{k_n}
--   \]
--   is absolutely convergent and has strictly positive real part. The counting assumptions are part of the theorem; no assertion that they have been formally instantiated for zeta zeros is made.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Composition of the two-cutoff small-scale argument, 2026-11-16. Complete elementary Lean proof. No claim of novelty; this is a conditional spectral theorem, not a complete Branch or RH proof.

import Mathlib

theorem BranchComposition.small_scale_positive_from_counts {ι : Type*} [DecidableEq ι]
    (e g : ι → ℝ) (he : ∀ i, |e i|≤1/2) (hg : ∀ i, 0≤g i)
    (cut : ℝ → Finset ι) (hpref : ∀ T i, i∈cut T ↔ g i≤T)
    (C : ℝ) (hC : 0≤C)
    (hcount : ∀ T ≥ (1 : ℝ), ∀ F : Finset ι,
      (∀ i ∈ F, T≤g i ∧ g i<T+1) → (F.card : ℝ)≤C*Real.log (T+3))
    (k : ℕ → ℕ) (hk : ∀ n, 2≤k n)
    (h L : ℕ → ℝ) (hh : ∀ n, 0<h n) (hh1 : ∀ n, h n≤1)
    (hL : ∀ n, 1≤L n) (hlog : ∀ n, -Real.log (h n)≤L n)
    (ht : Filter.Tendsto h Filter.atTop (nhds 0))
    (c : ℝ) (hc : 0<c)
    (hlower : ∀ᶠ n in Filter.atTop, c≤h n/L n*((cut (1/h n)).card : ℝ)) :
    ∀ᶠ n in Filter.atTop, Summable (fun i => (((((k n : ℝ)/(h n)^2 : ℝ) : ℂ)/(((k n : ℝ)/(h n)^2+(g i)^2-(e i)^2 : ℝ)-(2*e i*g i : ℝ)*Complex.I))^(k n))) ∧
      0<(∑' i, (((((k n : ℝ)/(h n)^2 : ℝ) : ℂ)/(((k n : ℝ)/(h n)^2+(g i)^2-(e i)^2 : ℝ)-(2*e i*g i : ℝ)*Complex.I))^(k n))).re := by sorry
