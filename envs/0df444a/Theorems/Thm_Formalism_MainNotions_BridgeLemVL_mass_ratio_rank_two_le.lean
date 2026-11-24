-- Prove2me | Theorems.Thm_Formalism_MainNotions_BridgeLemVL_mass_ratio_rank_two_le
-- name    : Formalism.MainNotions.BridgeLemVL.mass_ratio_rank_two_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:17:00.323331+00:00
-- url     : https://prove2.me/theorems/8c41a83d-cfd7-4ffa-aba6-933b2f99d221
-- title:
--   Bridge Lem VL: mass ratio rank two le
-- statement:
--   The Bridge Lem VL construction uses the mass ratio rank two le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVL.lean#L91-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVL.lean#L91-L109

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemVL
open NumberField Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.MainNotions.BridgeLemVL.mass_ratio_rank_two_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    Formalism.HermitianLatticesTheory.massRatioRightSide K 2 ≤ ((Formalism.HermitianLatticesTheory.vInv K / Real.pi) ^ 2) ^ Formalism.HermitianLatticesTheory.fDeg K *
      Real.exp (2 * ((Module.finrank ℚ K : ℝ) * Z2)) := by sorry
