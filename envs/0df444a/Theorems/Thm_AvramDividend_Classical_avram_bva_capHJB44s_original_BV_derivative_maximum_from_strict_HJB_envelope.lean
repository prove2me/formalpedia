-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB44s_original_BV_derivative_maximum_from_strict_HJB_envelope
-- name    : AvramDividend.Classical.avram_bva_capHJB44s_original_BV_derivative_maximum_from_strict_HJB_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:06:11.056359+00:00
-- url     : https://prove2.me/theorems/0de99ebb-cd84-4443-a5bb-31586048c537
-- title:
--   Compact derivative maximum absorbed by strict interior HJB loss envelope with epsilon endpoint localised
-- statement:
--   True BV source compact derivative bootstrap: control derivative on the small closed positive reserve band epsilon/2 through epsilon by B, and assume any maxima on a larger positive band exist. On the strict epsilon-open segment (epsilon,b], a physical drift larger than the negative small jump moment yields d*w prime <= A + eta*M. For a derivative maximum below or at epsilon use local B; above epsilon use strict HJB and absorb eta into drift. Gives universal interior derivative bound without incorrectly assuming the generator condition at y=epsilon.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_capHJB44s_original_BV_derivative_maximum_from_strict_HJB_envelope
    (d η A B ε c : ℝ) (hd : η < d)
    (hε : 0 < ε) (hc : ε < c)
    (w : ℝ → ℝ)
    (hLocal : ∀ t ∈ Icc (ε / 2) ε, deriv w t ≤ B)
    (hMax : ∀ b ∈ Ioo ε c,
      ∃ s ∈ Icc (ε / 2) b,
        ∀ t ∈ Icc (ε / 2) b, deriv w t ≤ deriv w s)
    (hEnv : ∀ b ∈ Ioo ε c,
      ∀ s ∈ Ioc ε b,
      ∀ M : ℝ,
      (∀ t ∈ Icc (ε / 2) b, deriv w t ≤ M) →
      d * deriv w s ≤ A + η * M) :
    ∀ t ∈ Ico (ε / 2) c,
      deriv w t ≤ max B (A / (d - η)) := by sorry
