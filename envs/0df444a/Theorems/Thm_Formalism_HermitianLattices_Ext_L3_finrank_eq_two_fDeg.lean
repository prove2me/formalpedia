-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_finrank_eq_two_fDeg
-- name    : Formalism.HermitianLattices.Ext.L3.finrank_eq_two_fDeg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:04:08.344633+00:00
-- url     : https://prove2.me/theorems/39599bbe-721b-484c-86b7-4e638f804fe0
-- title:
--   L3: finrank eq two f Deg
-- statement:
--   The L3 construction uses the finrank eq two f Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CovolumeIntegerLatticeEq.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CovolumeIntegerLatticeEq.lean#L21-L30

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CovolumeIntegerLatticeEq
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
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.HermitianLattices.Ext.L3.finrank_eq_two_fDeg (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    finrank ℚ K = 2 * Formalism.HermitianLatticesTheory.fDeg K := by sorry
