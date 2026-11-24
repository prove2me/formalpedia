-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_standardBasis_coe
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.standardBasis_coe
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:31:41.692899+00:00
-- url     : https://prove2.me/theorems/206e8008-0bf2-4745-b04c-fd92c418b154
-- title:
--   Column Families: standard Basis coe
-- statement:
--   The Column Families construction uses the standard Basis coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/FiltrationMaximalQuotient.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/FiltrationMaximalQuotient.lean#L26-L28

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_MemSpanStandardIffProjZero
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_FiltrationMaximalQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Module
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.standardBasis_coe (hS : SBasis) (mu : Fin n → ℤ) (hmu : Dominant mu) (I : {I : TIdx mu // StdT I}) :
    ((standardBasis hS mu hmu I : ↥(SMu mu)) : GLCoord ℤ n) = brk mu I.1 := by sorry
