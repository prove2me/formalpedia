-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_gal_KEd_algebraMap
-- name    : Formalism.HermitianLattices.Ext.L3.gal_KEd_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:22.193028+00:00
-- url     : https://prove2.me/theorems/60b91fd0-d825-4efc-a871-4b1b8edf752c
-- title:
--   L3: gal KEd algebra Map
-- statement:
--   The L3 construction uses the gal KEd algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassLandD.lean#L168-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassLandD.lean#L168-L170

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandDA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Polynomial
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (w : K) (hw0 : w ≠ 0) (hw : star w = -w) (d : cmF K) [Fact (Irreducible (polE d))]
  [Fact (Irreducible (polKE d (skewSq w hw)))]

theorem Formalism.HermitianLattices.Ext.L3.gal_KEd_algebraMap (τ : KEd d (skewSq w hw) ≃ₐ[Ed d] KEd d (skewSq w hw)) (a : cmF K) :
    τ (algebraMap (cmF K) (KEd d (skewSq w hw)) a) = algebraMap (cmF K) (KEd d (skewSq w hw)) a := by sorry
