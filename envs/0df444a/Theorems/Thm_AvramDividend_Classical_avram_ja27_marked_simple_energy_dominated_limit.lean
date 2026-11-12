-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja27_marked_simple_energy_dominated_limit
-- name    : AvramDividend.Classical.avram_ja27_marked_simple_energy_dominated_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:30:52.267303+00:00
-- url     : https://prove2.me/theorems/609c7dc5-c350-4717-a43e-80de64338028
-- title:
--   Exact source mark-simple squared moments pass to a dominated real-mark limit
-- statement:
--   An abstract physical source convergence certificate: if the true compensated finite mark-simple approximants have exact squared moment E(k), a jointly dominating integrable squared envelope, and their squares converge almost everywhere to the original real-mark compensated integral, then the original second moment equals the limit of the known simple energies. No auxiliary probability space or mark first moment is used.
-- source:
--   Needed for 924b87ab and ec5fe7b6 exact original marked strip isometry; combines with genuinely physical count covariance and Borel spatial approximation. All convergence assumptions explicit and locally checkable.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja27_marked_simple_energy_dominated_limit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (F : ℕ → Ω → ℝ) (C g : Ω → ℝ) (E : ℕ → ℝ) (e : ℝ)
    (hMeas : ∀ k, AEStronglyMeasurable (fun ω => (F k ω) ^ 2) P)
    (hg : Integrable g P)
    (hDom : ∀ k, ∀ᵐ ω ∂P, ‖(F k ω) ^ 2‖ ≤ g ω)
    (hLim : ∀ᵐ ω ∂P,
      Tendsto (fun k => (F k ω) ^ 2) atTop (𝓝 ((C ω) ^ 2)))
    (hSqMom : ∀ k, (∫ ω, (F k ω) ^ 2 ∂P) = E k)
    (hEnergy : Tendsto E atTop (𝓝 e)) :
    (∫ ω, (C ω) ^ 2 ∂P) = e := by sorry
