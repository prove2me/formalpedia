-- Prove2me | Theorems.Thm_BanditAlgorithm_le_cam_cauchy_affinity
-- name    : BanditAlgorithm.le_cam_cauchy_affinity
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-19T01:47:09.666222+00:00
-- url     : https://prove2.me/theorems/3ca9cad5-b8ca-47dc-aba8-8727ea5ea1a9
-- title:
--   Le Cam's Cauchy–Schwarz inequality for the Hellinger affinity
-- statement:
--   For probability measures P and Q, let ν=P+Q and p=dP/dν, q=dQ/dν. Le Cam’s Cauchy–Schwarz inequality states that one half of the squared Hellinger affinity is at most the overlap integral: $\frac12(\int\sqrt{pq}\,dν)^2\le\int\min(p,q)\,dν$. This includes mutually singular and identical measures.
-- source:
--   Lattimore--Szepesvari, Bandit Algorithms (CUP 2020), proof of Theorem 14.2, Eq. (14.9), printed p. 191 / PDF p. 200.

import Mathlib.InformationTheory.KullbackLeibler.Basic

open MeasureTheory InformationTheory
open scoped ENNReal

theorem BanditAlgorithm.le_cam_cauchy_affinity {Ω : Type} {mΩ : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    (2 : ℝ≥0∞)⁻¹ *
        (∫⁻ ω, (P.rnDeriv (P + Q) ω * Q.rnDeriv (P + Q) ω) ^ (2⁻¹ : ℝ)
          ∂(P + Q)) ^ 2 ≤
      ∫⁻ ω, min (P.rnDeriv (P + Q) ω) (Q.rnDeriv (P + Q) ω) ∂(P + Q) := by sorry
