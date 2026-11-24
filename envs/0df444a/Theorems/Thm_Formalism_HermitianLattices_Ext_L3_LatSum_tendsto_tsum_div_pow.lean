-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LatSum_tendsto_tsum_div_pow
-- name    : Formalism.HermitianLattices.Ext.L3.LatSum.tendsto_tsum_div_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:14.427865+00:00
-- url     : https://prove2.me/theorems/2f048d42-a9b5-4bb7-8b8d-886827638ab3
-- title:
--   Lat Sum: tendsto tsum div pow
-- statement:
--   The Lat Sum construction uses the tendsto tsum div pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/TendstoTsumDivPow.lean#L36-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/TendstoTsumDivPow.lean#L36-L112

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoTsumDivPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module MeasureTheory Filter Topology Bornology Pointwise ZLattice
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LatSum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
variable {ι : Type*} [Fintype ι]

theorem Formalism.HermitianLattices.Ext.L3.LatSum.tendsto_tsum_div_pow (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set E} (hs₁ : IsBounded s)
    (hs₂ : MeasurableSet s) (hs₃ : μ (frontier s) = 0) {G : E → ℝ} (hG : Continuous G) :
    Tendsto (fun n : ℕ ↦ (∑' x : ↑(s ∩ (n : ℝ)⁻¹ • (L : Set E)), G x) / (n : ℝ) ^ finrank ℝ E)
      atTop (𝓝 ((∫ x in s, G x ∂μ) / covolume L μ)) := by sorry
