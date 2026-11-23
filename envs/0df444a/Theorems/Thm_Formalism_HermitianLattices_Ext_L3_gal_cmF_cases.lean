-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_gal_cmF_cases
-- name    : Formalism.HermitianLattices.Ext.L3.gal_cmF_cases
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:15:49.380287+00:00
-- url     : https://prove2.me/theorems/9409da3e-741d-438d-9a33-48db392b3c9a
-- title:
--   L3: gal cm F cases
-- statement:
--   The L3 construction uses the gal cm F cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassLandA.lean#L82-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassLandA.lean#L82-L97

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable (K : Type) [Field K] [NumberField K] [StarRing K]
variable {K}

theorem Formalism.HermitianLattices.Ext.L3.gal_cmF_cases (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (g : K ≃ₐ[cmF K] K) : g = 1 ∨ g = conjF K := by sorry
