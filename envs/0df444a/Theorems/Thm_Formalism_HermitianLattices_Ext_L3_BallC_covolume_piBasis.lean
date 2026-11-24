-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallC_covolume_piBasis
-- name    : Formalism.HermitianLattices.Ext.L3.BallC.covolume_piBasis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:44:44.226178+00:00
-- url     : https://prove2.me/theorems/15d6e1bf-12a3-44b7-b967-5c5160b259fa
-- title:
--   Ball C: covolume pi Basis
-- statement:
--   The Ball C construction uses the covolume pi Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FundamentalDomainPiBasis.lean#L85-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FundamentalDomainPiBasis.lean#L85-L92

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FundamentalDomainPiBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding MeasureTheory Module
open scoped Classical
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallC
variable (K : Type*) [Field K] [NumberField K] (ι : Type*) [Fintype ι]

theorem Formalism.HermitianLattices.Ext.L3.BallC.covolume_piBasis :
    ZLattice.covolume (Submodule.span ℤ (Set.range (piBasis K ι))) volume =
      ((2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K * Real.sqrt |(discr K : ℝ)|) ^ Fintype.card ι := by sorry
