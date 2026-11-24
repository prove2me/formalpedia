-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_finrank_cmF
-- name    : Formalism.HermitianLattices.Ext.L3.finrank_cmF
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:15:11.464178+00:00
-- url     : https://prove2.me/theorems/a4326cad-4359-429e-90f5-a8f50975210d
-- title:
--   L3: finrank cm F
-- statement:
--   The L3 construction uses the finrank cm F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassLandA.lean#L76-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassLandA.lean#L76-L80

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

theorem Formalism.HermitianLattices.Ext.L3.finrank_cmF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) : finrank (cmF K) K = 2 := by sorry
