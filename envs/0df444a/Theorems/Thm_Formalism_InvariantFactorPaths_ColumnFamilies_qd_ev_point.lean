-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_ev_point
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qd_ev_point
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:02:19.824328+00:00
-- url     : https://prove2.me/theorems/d654cc2e-08b0-41a7-a8d4-5f36da2406b5
-- title:
--   Column Families: qd ev point
-- statement:
--   The Column Families construction uses the qd ev point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestVectorsRationalSpan.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestVectorsRationalSpan.lean#L12-L19

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TranslatesSpanCanonical
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbBasisApply
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsRationalSpan
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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qd_ev_point (M : GLMod n) (nu : Fin n → ℤ) (x : M.ι → ℚ) {R' : Type} [CommRing R'] [Algebra ℚ R']
    (g : GL (Fin n) R') (i : M.ι) :
    evGLR (R := ℚ) g (qb_ev M ℚ nu x i) =
      Matrix.mulVec ((prMu M nu).map (Int.castRingHom R'))
        (Matrix.mulVec (M.A.map (evGL g)) (fun l => algebraMap ℚ R' (x l))) i := by sorry
