-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallC_psi_apply
-- name    : Formalism.HermitianLattices.Ext.L3.BallC.psi_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:11:22.058154+00:00
-- url     : https://prove2.me/theorems/f454710f-36b7-4606-a829-d0ca0a042122
-- title:
--   Ball C: psi apply
-- statement:
--   The Ball C construction uses the psi apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FundamentalDomainPiBasis.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FundamentalDomainPiBasis.lean#L27-L28

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

theorem Formalism.HermitianLattices.Ext.L3.BallC.psi_apply [IsEmpty {w : InfinitePlace K // w.IsReal}] (y : ι → mixedSpace K)
    (w : {w : InfinitePlace K // w.IsComplex}) (i : ι) : psi K ι y w i = (y i).2 w := by sorry
