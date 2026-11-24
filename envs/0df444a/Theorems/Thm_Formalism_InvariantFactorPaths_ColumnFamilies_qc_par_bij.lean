-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_par_bij
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qc_par_bij
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:21:15.037292+00:00
-- url     : https://prove2.me/theorems/0ef2a159-89f0-4b7e-b02f-7d76956aea99
-- title:
--   Column Families: qc par bij
-- statement:
--   The Column Families construction uses the qc par bij property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLDetUZpow.lean#L33-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLDetUZpow.lean#L33-L73

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qc_par_bij {i N : ℕ} : Function.Bijective (qc_par (i := i) (N := N)) := by sorry
