-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_brk_eq
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qa_brk_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:39:48.273409+00:00
-- url     : https://prove2.me/theorems/a2fe273b-9375-4b9e-82a9-0b2f0ecee8d1
-- title:
--   Column Families: qa brk eq
-- statement:
--   The Column Families construction uses the qa brk eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/ABridge.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/ABridge.lean#L35-L39

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qa_brk_eq {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) :
    brk mu I = ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) *
      algebraMap (MvPolynomial (Fin n × Fin n) ℤ) (GLCoord ℤ n) (rename Prod.swap (qa_P ℤ I)) := by sorry
