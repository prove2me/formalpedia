-- Prove2me | Theorems.Thm_AuctionDuration_ClearingError_Supplement_lemma_C_1
-- name    : AuctionDuration.ClearingError.Supplement.lemma_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:50:01.012307+00:00
-- url     : https://prove2.me/theorems/e18fd07c-4c5f-4a96-b460-02c811381e3d
-- title:
--   Lemma C.1 — uniform reference and controlled supremum moments
-- statement:
--   Fix the same bounded-intensity canonical game with $h>0$. For $s\in[0,h]$ and $x\in\mathbb N^2$, set $X^{s,x}_u=x+X_u-X_s$ for $u\in[s,h]$, and let $\|\cdot\|$ denote the Euclidean norm (the source's subscript 1). For every real $\rho>0$, there is a finite constant $C_\rho>0$, depending only on the fixed horizon and intensity parameters, such that simultaneously
--   $$
--   E\!\left[\sup_{s\le u\le h}\|X^{s,x}_u\|^\rho\right]\le C_\rho(1+|x_a|^\rho+|x_b|^\rho),
--   $$
--   $$
--   E^{P^{a,b}}\!\left[\sup_{s\le u\le h}\|X^{s,x}_u\|^\rho\right]\le C_\rho(1+|x_a|^\rho+|x_b|^\rho)
--   \quad\text{for all }(a,b)\in\mathcal U^2.
--   $$
--   The same constant works for every start time, starting count pair and admissible control pair. Both supremum functionals are integrable; the actual supremum sets are nonempty and bounded. This estimate supports Theorem C.1 without restricting moment orders to integers.
--
--   Differences from the source:
--   - reading: canonical compensated pair on p.23 → independent reference Poisson coordinates; reason: the multivariate point-process construction and signed compound-Poisson representation on p.29 use no common jumps; compensators alone would not fix a unique law
--   - encoding: all s∈[0,h] and x∈N² → nonnegative real start time bounded by h, two natural coordinates, real rpow; reason: same complete time and state domains, including s=h and noninteger ρ
--   - encoding: Euclidean supremum expectations → actual nonempty bounded supremum sets and explicit integrability under both laws; reason: the source p.24 names its Euclidean norm with subscript 1; explicit guards prevent junk real suprema or Bochner expectations
-- source:
--   Jusselin, Mastrolia & Rosenbaum, Optimal auction duration: a price formation viewpoint, arXiv:1906.01713v3, https://arxiv.org/abs/1906.01713v3, p.27, Lemma C.1; pp.12,22–24, standing assumptions

import Mathlib
import Definitions.Def_AuctionDuration_ClearingError_Supplement_Canonical

open MeasureTheory Set
open scoped NNReal

namespace AuctionDuration.ClearingError.Supplement

/-- Lemma C.1, p.27. One constant for both laws, uniform in s,x and controls,
for EVERY positive real moment order, including noninteger orders below one. -/
theorem lemma_C_1 (G : Game) (hG : G.Standing) (hh : 0 < G.h) :
    ∀ ρ : ℝ, 0 < ρ → ∃ C : ℝ, 0 < C ∧
      ∀ s : ℝ≥0, (s : ℝ) ≤ G.h → ∀ x : Fin 2 → ℕ,
        (∀ ω : Sample, (momentRange G s x ρ ω).Nonempty ∧
          BddAbove (momentRange G s x ρ ω)) ∧
        Integrable (supremumMoment G s x ρ) G.P ∧
        (∫ ω, supremumMoment G s x ρ ω ∂G.P) ≤
          C * (1 + (x 0 : ℝ) ^ ρ + (x 1 : ℝ) ^ ρ) ∧
        ∀ a b : Process, G.Admissible a → G.Admissible b →
          IsProbabilityMeasure (G.law a b) ∧
          Integrable (supremumMoment G s x ρ) (G.law a b) ∧
          (∫ ω, supremumMoment G s x ρ ω ∂(G.law a b)) ≤
            C * (1 + (x 0 : ℝ) ^ ρ + (x 1 : ℝ) ^ ρ) := by sorry

end AuctionDuration.ClearingError.Supplement
