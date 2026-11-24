-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_algebraMap_inj
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qa_algebraMap_inj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:39:13.16881+00:00
-- url     : https://prove2.me/theorems/815be3d5-812f-428e-9a0b-b36ff5bb9dd2
-- title:
--   Column Families: qa algebra Map inj
-- statement:
--   The Column Families construction uses the qa algebra Map inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/ABridge.lean#L49-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/ABridge.lean#L49-L52

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaExpEqBidetExp
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

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
open Formalism.GradedWeylDivisibility

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qa_algebraMap_inj (R : Type*) [CommRing R] [IsDomain R] (n : ℕ) :
    Function.Injective (algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)) := by sorry
