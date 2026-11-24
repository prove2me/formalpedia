-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LatSum_map_equivFun
-- name    : Formalism.HermitianLattices.Ext.L3.LatSum.map_equivFun
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:48.170492+00:00
-- url     : https://prove2.me/theorems/97ddbeda-656a-48f9-b4ce-7fbe96851e20
-- title:
--   Lat Sum: map equiv Fun
-- statement:
--   The Lat Sum construction uses the map equiv Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/TendstoTsumDivPow.lean#L14-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/TendstoTsumDivPow.lean#L14-L34

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

theorem Formalism.HermitianLattices.Ext.L3.LatSum.map_equivFun (μ : Measure E) [μ.IsAddHaarMeasure] (b : Basis ι ℤ L) :
    μ.map (b.ofZLatticeBasis ℝ L).equivFunL = ENNReal.ofReal (covolume L μ) • volume := by sorry
