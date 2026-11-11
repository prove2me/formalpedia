-- Prove2me | solution 1 for levy_foundations_public_tilted_cofinal_mass_sequence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T13:25:28.517528+00:00
-- url     : https://prove2.me/submissions/1930dba6-20f2-4a5b-92ce-0a1a52374f44

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.NhdsWithin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Shift an explicit reciprocal small-time sequence past an eventual mass bound. -/
theorem solution (S : ConvolutionSemigroup) (C : ℝ≥0)
    (hmass : ∀ᶠ (t : {t : ℝ // 0 < t}) in comap Subtype.val (𝓝[>] (0 : ℝ)),
      S.tiltedScaledMeasure t Set.univ ≤ (C : ℝ≥0∞)) :
    ∃ (t_seq : ℕ → {t : ℝ // 0 < t}),
      Tendsto (fun n => (t_seq n).val) atTop (𝓝 0) ∧
      ∀ n, S.tiltedScaledMeasure (t_seq n) Set.univ ≤ (C : ℝ≥0∞) := by
  set s : ℕ → {t : ℝ // 0 < t} := fun n => ⟨1/(n+2), by positivity⟩ with hs_def
  have hs_tendsto : Tendsto (fun n => (s n).val) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := h.comp (tendsto_add_atTop_nat 1)
    refine h2.congr (fun n => ?_)
    simp [s, Nat.cast_add, Nat.cast_one]
    ring
  have hs_filter : Tendsto s atTop (Filter.comap Subtype.val (𝓝[>] (0 : ℝ))) := by
    rw [Filter.tendsto_comap_iff]
    refine tendsto_nhdsWithin_iff.mpr ⟨hs_tendsto, ?_⟩
    exact Filter.Eventually.of_forall (fun n => (s n).prop)
  have hev : ∀ᶠ n in atTop, S.tiltedScaledMeasure (s n) Set.univ ≤ (C : ℝ≥0∞) :=
    hs_filter.eventually hmass
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hev
  refine ⟨(fun n => s (n + n₀)), ?_, ?_⟩
  · exact hs_tendsto.comp (tendsto_add_atTop_nat n₀)
  · intro n
    exact hn₀ (n + n₀) (Nat.le_add_left n₀ n)
