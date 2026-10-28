-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_uncapped_firstClosedHit_stopping_and_event
-- name    : AvramDividend.Classical.reflectedSup_uncapped_firstClosedHit_stopping_and_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:15:51.981192+00:00
-- url     : https://prove2.me/theorems/282d8c8f-7936-4533-a194-39d91023b34f
-- title:
--   Actual unbounded-horizon reflected first closed-level hit is a stopping time with exact finite-time entrance events
-- statement:
--   For the actual reflected spectrally negative Lévy process, choose any sequence of deterministic horizons cofinal towards infinity and let τ be the extended-real supremum of the corresponding true capped closed-level first-passage times. Then τ is a stopping time under the original filtration, and for every path ω and every finite t, τ(ω)≤t exactly when R_s(ω)≥x for some s≤t. This is a genuine unbounded-horizon first closed-level entrance stopping clock: when the reflected path never reaches x, τ=∞. The result combines the accepted countable-capped stopping-time closure, the cofinal-horizon pathwise equivalence, and actual reflected-path upper semicontinuity on every compact prefix. No right-continuity assumption on the filtration or assumed stopping selector is needed. It remains a P-filtration theorem and does not assert an Itô excursion n-Markov law.
-- source:
--   Accepted Prove2Me reflectedSup_countable_caps_hit_stoppingTime, usc_cofinal_capped_hit_sup_le_iff_level_hit, reflectedSup_upperSemicontinuousOn_Icc.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_reflectedSup_countable_caps_hit_stoppingTime
import Theorems.Thm_AvramDividend_Classical_usc_cofinal_capped_hit_sup_le_iff_level_hit
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.reflectedSup_uncapped_firstClosedHit_stopping_and_event
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (caps : ℕ → ℝ≥0)
    (hcofinal : ∀ t : ℝ≥0, ∃ n : ℕ, t < caps n)
    (x : ℝ) :
    IsStoppingTime 𝓕 (fun ω : Ω =>
      ⨆ n : ℕ, WithTop.some
        (sInf ((Icc (0 : ℝ≥0) (caps n) ∩
          (fun t : ℝ≥0 => reflectedSup X t ω) ⁻¹' Ici x) ∪ {caps n}))) ∧
    ∀ ω : Ω, ∀ t : ℝ≥0,
      (⨆ n : ℕ, WithTop.some
        (sInf ((Icc (0 : ℝ≥0) (caps n) ∩
          (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {caps n}))) ≤
          (t : WithTop ℝ≥0) ↔
        ∃ s : ℝ≥0, s ≤ t ∧ x ≤ reflectedSup X s ω := by sorry
