-- Prove2me | Theorems.Thm_BauerleRiederMDP_MeanRisk_example_C_2_2_b
-- name    : BauerleRiederMDP.MeanRisk.example_C_2_2_b
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:28:13.206887+00:00
-- url     : https://prove2.me/theorems/3c3e0c0d-7f77-4ae7-9169-a072764a105d
-- title:
--   Example C.2.2 b), eq. (C.1) — $\mathrm{AVaR}_\gamma(X)=\inf_b\{b+\frac1{1-\gamma}\mathbb E[(X+b)^-]\}$, minimum at $\mathrm{VaR}_\gamma(X)$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $X\in L^1(\Omega,\mathcal F,\mathbb P)$ and $\gamma\in(0,1)$. The Average-Value-at-Risk $\mathrm{AVaR}_\gamma(X)=\frac1{1-\gamma}\int_\gamma^1\mathrm{VaR}_u(X)\,du$ is the value of the convex optimization problem
--
--   $$
--   \mathrm{AVaR}_\gamma(X)=\inf_{b\in\mathbb R}\Big\{b+\frac{1}{1-\gamma}\,\mathbb E\big[(X+b)^-\big]\Big\},
--   $$
--
--   and the minimum is attained at $b^*=\mathrm{VaR}_\gamma(X)$. Here $y^-=\max\{-y,0\}$.
--
--   This representation turns the mean-risk problem (MR) into the family of Markov decision problems $P(\lambda,b)$ of §4.7: it is the bridge between the risk measure and dynamic programming.
--
--   Differences from the source:
--   - encoding: X ∈ L¹(Ω, F, IP) (equivalence classes) → a function X with Integrable X P; reason: both sides depend only on the law of X; same instances
--   - encoding: the minimum is attained at b* = VaR_γ(X) → IsMinOn of the objective on ℝ at VaR P γ X; reason: Lean convention; same statement
--   - encoding: inf over b ∈ ℝ → the real ⨅ b; reason: the family is bounded below by −E[X], so the real ⨅ is the infimum
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Example C.2.2 b), eq. (C.1) and the sentence after it, p.368 (PDF p.373)

import Mathlib
import Definitions.Def_BauerleRiederMDP_MeanRisk_VaR
import Definitions.Def_BauerleRiederMDP_MeanRisk_AVaR

open MeasureTheory

namespace BauerleRiederMDP.MeanRisk

/-- Bäuerle & Rieder (2011), Example C.2.2 b), eq. (C.1), p.368 (PDF 373): for
`X ∈ L¹(Ω, F, ℙ)` and `γ ∈ (0,1)`, the Average-Value-at-Risk is the value of the optimization problem
`AVaR_γ(X) = inf_{b ∈ ℝ} { b + (1/(1 − γ)) 𝔼[(X + b)⁻] }`,
and the minimum is attained at `b* = VaR_γ(X)`.

**Formalization Note.** `(X + b)⁻ = max (−(X + b)) 0`. The infimum is the real `⨅`; the second
conjunct says that `VaR_γ(X)` minimizes the objective over all of `ℝ`. -/
theorem example_C_2_2_b {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    AVaR P γ X = (⨅ b : ℝ, (b + (1 - γ)⁻¹ * ∫ ω, max (-(X ω + b)) 0 ∂P)) ∧
      IsMinOn (fun b : ℝ => b + (1 - γ)⁻¹ * ∫ ω, max (-(X ω + b)) 0 ∂P) Set.univ (VaR P γ X) := by sorry

end BauerleRiederMDP.MeanRisk
