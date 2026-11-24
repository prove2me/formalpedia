-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_ev_inv
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qd_ev_inv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:02:43.03266+00:00
-- url     : https://prove2.me/theorems/6c0335ae-3a38-41f5-841a-40f3a2213aee
-- title:
--   Column Families: qd ev inv
-- statement:
--   The Column Families construction uses the qd ev inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestVectorsRationalSpan.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestVectorsRationalSpan.lean#L21-L25

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TranslatesSpanCanonical
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbBasisApply
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsRationalSpan
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qd_ev_inv (M : GLMod n) (la nu : Fin n → ℤ) (x : M.ι → ℚ) (hx : IsHighest M ℚ la x)
    {R' : Type} [CommRing R'] [Algebra ℚ R'] (g u : GL (Fin n) R') (hu1 : ∀ a, u.val a a = 1)
    (hu2 : ∀ a b, b < a → u.val a b = 0) (i : M.ι) :
    evGLR (R := ℚ) (g * u) (qb_ev M ℚ nu x i) = evGLR (R := ℚ) g (qb_ev M ℚ nu x i) := by sorry
