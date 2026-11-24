-- Prove2me | Theorems.Thm_AAInvW_lf_unit_entry
-- name    : AAInvW.lf_unit_entry
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:44:49.472798+00:00
-- url     : https://prove2.me/theorems/4d0bac5f-a37f-4c0b-a680-271c51169b76
-- title:
--   AAInv W: lf unit entry
-- statement:
--   The AAInv W construction uses the lf unit entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SubsetUpperHessenberg.lean#L38-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SubsetUpperHessenberg.lean#L38-L46

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
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

theorem AAInvW.lf_unit_entry (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hg : inUH (Hpk k r) g) (b p : Fin (2 * r + k + 1)) :
    ∑ t, star (g t b) * (hkEps k r t * g (hkSig k r t) p) = Hpk k r b p := by sorry
