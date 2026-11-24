-- Prove2me | Theorems.Thm_Formalism_MainNotions_BridgeLemVN_mass_std_one_le
-- name    : Formalism.MainNotions.BridgeLemVN.mass_std_one_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T09:55:02.63481+00:00
-- url     : https://prove2.me/theorems/05e09e50-9ace-4f88-9200-ed30532d3cf8
-- title:
--   Bridge Lem VN: mass std one le
-- statement:
--   The Bridge Lem VN construction uses the mass std one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVN.lean#L134-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVN.lean#L134-L142

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVC
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemVN
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne Formalism.MainNotions.BridgeLemVR
  Formalism.MainNotions.BridgeLemVC
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.MainNotions.BridgeLemVN.mass_std_one_le (hK : IsCMUnram K) :
    mass (stdForm K 1) (stdLat K 1) ≤ ((classNumber K * 2 ^ fDeg K : ℕ) : ℝ) := by sorry
