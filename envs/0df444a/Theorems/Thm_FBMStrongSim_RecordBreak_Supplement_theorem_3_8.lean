-- Prove2me | Theorems.Thm_FBMStrongSim_RecordBreak_Supplement_theorem_3_8
-- name    : FBMStrongSim.RecordBreak.Supplement.theorem_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T22:30:12.244798+00:00
-- url     : https://prove2.me/theorems/c5efe16d-c795-4398-b84f-5fcdad3a8420
-- title:
--   Theorem 3.8 — Hölder error after the last record
-- statement:
--   Let $B$ be the continuous version of a centered fBM on $[0,1]$ with $1/2<H<1$, choose $1/2<\alpha<H$, $0<\delta<H-\alpha$, and $\rho>0$. Let $N$ be the published last record level, using threshold $\rho2^{-(H-\delta)k}$, and $B_n$ the published linear interpolation. Almost surely, simultaneously for every $n>N$,
--   $$\|B-B_n\|_\alpha\le\rho2^{2-\alpha}\frac{2^{-(H-\alpha-\delta)(n+1)}}{1-2^{-(H-\alpha-\delta)}}.$$
--   This companion to the goal controls the stronger error norm needed for pathwise differential equations.
--
--   Differences from the source:
--   - encoding: the continuous modification of fBM → published IsFBM plus almost-sure continuity, with an almost-sure conclusion; reason: the convention on p. 5 is the same as in the published goal; covariance and continuity imply B(0)=0 almost surely
--   - encoding: a homogeneous Hölder seminorm inequality → its pointwise increment inequality on [0,1]; reason: equivalent for positive α; it avoids a real supremum that defaults to zero on an unbounded set
--   - reading: ρ=2(ν+ν*) with ν,ν*>0 → an arbitrary ρ>0 in the same lastRecord threshold; reason: these parameter choices range over all positive ρ; choosing ν=ν*=ρ/4 recovers each Lean threshold without changing the source claim
-- source:
--   Chen, Dong & Ni, ε-Strong simulation of fractional Brownian motion and related stochastic differential equations, arXiv:1902.07824v1, p. 13, Theorem 3.8

import Mathlib
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_HolderModel

namespace FBMStrongSim.RecordBreak.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Theorem 3.8 (p.13), with the same lastRecord as the published goal. -/
theorem theorem_3_8 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {H alpha delta rho : ℝ} (hH : 1 / 2 < H) (hH1 : H < 1)
    (ha : 1 / 2 < alpha) (haH : alpha < H) (hd : 0 < delta) (hdHa : delta < H - alpha)
    (hrho : 0 < rho) {B : ℝ → Ω → ℝ} (hB : IsFBM H B P)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => B t ω) (Set.Icc 0 1)) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, lastRecord rho H delta (fun s => B s ω) < n →
      HolderBound alpha
        (rho * (2 : ℝ) ^ (2 - alpha) * (2 : ℝ) ^ (-(H - alpha - delta) * ((n : ℝ) + 1)) /
          (1 - (2 : ℝ) ^ (-(H - alpha - delta))))
        (fun t => B t ω - interp (fun s => B s ω) n t) := by sorry

end FBMStrongSim.RecordBreak.Supplement
