-- Prove2me | Theorems.Thm_FBMStrongSim_RecordBreak_last_record_finite_ae
-- name    : FBMStrongSim.RecordBreak.last_record_finite_ae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:37.750394+00:00
-- url     : https://prove2.me/theorems/dad965d3-fe95-45cd-8509-1941979be6a5
-- title:
--   Proof of Theorem 3.5, pp. 11–12 — by Borel–Cantelli, the last record level N is finite almost surely
-- statement:
--   Let $B$ be a fractional Brownian motion on $[0,1]$ with Hurst index $H\in(0,1)$, fix $\delta\in(0,H)$ and $\rho>0$, and let
--   $$N=\sup\Big\{k\ge1:\max_{0\le j\le 2^{k-1}-1}|a^k_j-b^k_j|\ge\rho\,2^{-(H-\delta)k}\Big\}$$
--   be the last record-breaking level ($\sup\emptyset=0$). Then
--   $$\mathbb P(N<\infty)=1,$$
--   i.e. almost surely records are broken at only finitely many levels.
--
--   This is condition C1) of the record-breaker scheme (p. 7): beyond a random but finite level no further records occur.
--
--   **Formalization Note** $N$ takes values in $\mathbb N\cup\{\infty\}$ with $N=\infty$ when records occur at infinitely many levels. Any $\rho>0$ is admitted: the paper's $\rho=2(\nu+\nu^*)$ with $\nu,\nu^*>0$ ranges over all of $(0,\infty)$.
-- source:
--   Chen, Dong & Ni, ε-Strong simulation of fractional Brownian motion and related stochastic differential equations, arXiv:1902.07824v1, pp. 11–12, proof of Theorem 3.5

import Mathlib
import Definitions.Def_FBMStrongSim_RecordBreak_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FBMStrongSim.RecordBreak

/-- Proof of Theorem 3.5, pp. 11–12: for every `ρ > 0`, almost surely only finitely many levels
break a record, i.e. the last record level `N` is finite almost surely. -/
theorem last_record_finite_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {H delta rho : ℝ} (hH0 : 0 < H) (hH1 : H < 1) (hdelta0 : 0 < delta)
    (hdeltaH : delta < H) (hrho : 0 < rho) {B : ℝ → Ω → ℝ} (hB : IsFBM H B P) :
    ∀ᵐ ω ∂P, lastRecord rho H delta (fun s => B s ω) < ⊤ := by sorry

end FBMStrongSim.RecordBreak
