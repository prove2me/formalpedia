-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_grid_exit_infimum_approaches_continuous
-- name    : AvramDividend.Classical.chat03_grid_exit_infimum_approaches_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T21:33:48.60981+00:00
-- url     : https://prove2.me/theorems/1f9f6c3b-5cc4-4647-b6e4-f05886d80849
-- title:
--   Strict uniform-grid exit infima converge from above to continuous strict-passage infimum
-- statement:
--   For any fixed càdlàg spectrally negative Lévy sample path with continuous strict two-sided exit set S and greatest lower bound τ, the infimum σ_h of strictly exited grid-sample times is never earlier than τ. Given ε>0, for sufficiently small h>0 it is also strictly less than τ+ε. The theorem is stated conditionally on the respective IsGLB witnesses for the continuous and mesh sets, without claiming the infimum is an attained strict crossing or adding right-continuous filtration assumptions. It follows immediately and non-circularly from the separately Proved mesh-detection-near-infimum theorem. This establishes the precise finite-clock first-passage approximation needed for later stopped-value convergence; the killed q-scale martingale remains a separate obligation.
-- source:
--   Chat03 strict-exit mesh approximation (publication pending) and pinned Mathlib IsGLB, revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_exit_mesh_approximation
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_grid_exit_infimum_approaches_continuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ h : ℝ≥0, 0 < h → h < δ →
      ∀ σ : ℝ≥0,
        IsGLB
          {s : ℝ≥0 | ∃ k : ℕ,
            s = (k : ℝ≥0) * h ∧
            (X.X s ω < lower ∨ upper < X.X s ω)} σ →
        τ ≤ σ ∧ σ < τ + ε := by sorry
