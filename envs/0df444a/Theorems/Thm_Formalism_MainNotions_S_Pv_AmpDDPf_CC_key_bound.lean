-- Prove2me | Theorems.Thm_Formalism_MainNotions_S_Pv_AmpDDPf_CC_key_bound
-- name    : Formalism.MainNotions.S.Pv.AmpDDPf.CC.key_bound
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:10:31.151903+00:00
-- url     : https://prove2.me/theorems/0181f702-d3e0-486e-a090-b07f7946e791
-- title:
--   CC: key bound
-- statement:
--   The CC construction uses the key bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/CompactCellConvergence/KeyBound.lean#L7-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/CompactCellConvergence/KeyBound.lean#L7-L34

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_CompactCellConvergence_KeyBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Pv Formalism.MainNotions.S.Pv.AmpDDPf Formalism.MainNotions.S.Pv.AmpDDPf.CC

theorem Formalism.MainNotions.S.Pv.AmpDDPf.CC.key_bound {X Y M K b : ℝ} {E : ℕ} (hX : 1 ≤ X) (hY : 1 ≤ Y) (hM : 1 ≤ M) (hK : 0 < K) (hE : 0 < E)
    (hb : 0 ≤ b) (h : X + Y ≤ K * M ^ E) :
    M ^ (-b) ≤ K ^ (b / E) * (X ^ (-(b / (2 * E))) * Y ^ (-(b / (2 * E)))) := by sorry
