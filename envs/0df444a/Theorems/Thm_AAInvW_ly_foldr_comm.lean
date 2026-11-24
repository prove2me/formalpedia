-- Prove2me | Theorems.Thm_AAInvW_ly_foldr_comm
-- name    : AAInvW.ly_foldr_comm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:27:36.169272+00:00
-- url     : https://prove2.me/theorems/5f1c33f2-4124-4b7c-962e-d3effa4246d2
-- title:
--   AAInv W: ly foldr comm
-- statement:
--   The AAInv W construction uses the ly foldr comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/LyQminorLeft.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/LyQminorLeft.lean#L24-L31

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAaVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_LyQminorLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

theorem AAInvW.ly_foldr_comm {X E : Type*} (L : (X → E) → (X → E)) (l : List ((X → E) → (X → E)))
    (hl : ∀ T ∈ l, ∀ f, T (L f) = L (T f)) (f : X → E) :
    l.foldr (fun T h => T h) (L f) = L (l.foldr (fun T h => T h) f) := by sorry
