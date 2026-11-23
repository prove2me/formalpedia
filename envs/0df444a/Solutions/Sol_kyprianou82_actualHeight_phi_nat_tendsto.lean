-- Prove2me | solution 1 for kyprianou82_actualHeight_phi_nat_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:48:51.614703+00:00
-- url     : https://prove2.me/submissions/1ff26af7-551e-4c9c-bba9-49c41ac9a6e7

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_kyprianou82_phi_domain_bridge
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
  (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
  (hW : HasSourceScaleFamily ψ W)
    : Tendsto (fun n : ℕ => Phi ψ (1 / ((n : ℝ) + 1))) atTop (nhds (Phi ψ 0)) := by
  let qn := fun n : ℕ => 1 / ((n : ℝ) + 1)
  let hq_tendsto : Tendsto qn atTop (nhds 0) := by
    simpa [qn] using (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0))
  have hqn_nonneg : ∀ n : ℕ, 0 ≤ qn n := by
    intro n
    dsimp [qn]
    positivity
  have hqn_pos : ∀ n : ℕ, 0 < qn n := by
    intro n
    dsimp [qn]
    positivity
  let hbridge := kyprianou82_phi_domain_bridge P D ψ W hψ hW
  let hm0 := ((hW 0 le_rfl).1).2.1
  let hΦ0 : 0 ≤ Phi ψ 0 := hm0.1
  let hψΦ0 : ψ (Phi ψ 0) = 0 := hm0.2
  let hlower (n : ℕ) : Phi ψ 0 ≤ Phi ψ (qn n) := by
    by_contra hn
    let hlt := lt_of_not_ge hn
    let ht := ((hbridge (qn n) (hqn_nonneg n)).2 (Phi ψ 0) hΦ0).mp hlt
    rw [hψΦ0] at ht
    have hqn : 0 < qn n := hqn_pos n
    linarith
  let hPhiTendsto : Tendsto (fun n => Phi ψ (qn n)) atTop (nhds (Phi ψ 0)) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      exact Filter.Eventually.of_forall fun n => lt_of_lt_of_le ha (hlower n)
    · intro b hb
      let β := (Phi ψ 0 + b) / 2
      have hβgt : Phi ψ 0 < β := by dsimp [β]; linarith
      have hβlt : β < b := by dsimp [β]; linarith
      have hβ0 : 0 ≤ β := le_trans hΦ0 hβgt.le
      have hψβ : 0 < ψ β := ((hbridge 0 le_rfl).2 β hβ0).mp hβgt
      have hev : ∀ᶠ n in atTop, qn n < ψ β := hq_tendsto (Iio_mem_nhds hψβ)
      filter_upwards [hev] with n hn
      have hPhil : Phi ψ (qn n) < β :=
        ((hbridge (qn n) (hqn_nonneg n)).2 β hβ0).mpr hn
      exact lt_trans hPhil hβlt
  simpa [qn] using hPhiTendsto
