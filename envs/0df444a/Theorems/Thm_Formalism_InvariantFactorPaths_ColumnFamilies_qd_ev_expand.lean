-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_ev_expand
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qd_ev_expand
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:01:29.516845+00:00
-- url     : https://prove2.me/theorems/4dfb0caf-0ca0-4865-9a8d-21acdc11948f
-- title:
--   Column Families: qd ev expand
-- statement:
--   The Column Families construction uses the qd ev expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestVectorsRationalSpan.lean#L50-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestVectorsRationalSpan.lean#L50-L69

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
variable [NeZero n]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qd_ev_expand {M : GLMod n} (CF : ColFam M) (a : qb_Idx CF → ℚ) (nu : Fin n → ℤ)
    (hmax : ∀ y, a y ≠ 0 → DomLE nu (CF.mu y.1) → CF.mu y.1 = nu) (i : M.ι) :
    qb_ev M ℚ nu (∑ y, a y • qb_vecF CF ℚ y) i =
      ∑ j : {j : CF.J // CF.mu j = nu}, ((CF.ph j.1 i (canT (CF.mu j.1)) : ℤ) : ℚ) • qd_f CF a j.1 := by sorry
