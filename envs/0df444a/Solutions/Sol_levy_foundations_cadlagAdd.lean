-- Prove2me | solution 1 for levy_foundations_cadlagAdd
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T00:27:55.158287+00:00
-- url     : https://prove2.me/submissions/4d9f9e22-23b5-49e2-adf4-c5b839b8a825

import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
import Definitions.Def_levy_foundations_isCadlag

open Filter Set Topology
open scoped NNReal

theorem solution {f g : ℝ≥0 → ℝ}
    (hf : LevyFoundations.isCadlag f)
    (hg : LevyFoundations.isCadlag g) :
    LevyFoundations.isCadlag (fun t => f t + g t) := by
  intro t
  obtain ⟨hf1, a, ha⟩ := hf t
  obtain ⟨hg1, b, hb⟩ := hg t
  exact ⟨hf1.add hg1, a + b, ha.add hb⟩
