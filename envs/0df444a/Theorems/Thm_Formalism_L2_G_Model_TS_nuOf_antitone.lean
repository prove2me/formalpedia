-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_nuOf_antitone
-- name    : Formalism.L2.G.Model.TS.nuOf_antitone
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:30.827899+00:00
-- url     : https://prove2.me/theorems/13c56fdf-6313-486d-832e-155e2836968f
-- title:
--   TS: nu Of antitone
-- statement:
--   The TS construction uses the nu Of antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/FormSK.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/FormSK.lean#L30-L32

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FormSK
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FormSK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.InvariantFactorPaths.INST

theorem Formalism.L2.G.Model.TS.nuOf_antitone {m : ℕ} {lam : Fin (m + 1) → ℤ} (hl : Antitone lam) : Antitone (nuOf lam) := by sorry
