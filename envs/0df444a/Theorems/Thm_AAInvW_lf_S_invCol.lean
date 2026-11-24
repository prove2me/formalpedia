-- Prove2me | Theorems.Thm_AAInvW_lf_S_invCol
-- name    : AAInvW.lf_S_invCol
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:45:00.228875+00:00
-- url     : https://prove2.me/theorems/68770295-1aca-4f09-a159-0873f4868273
-- title:
--   AAInv W: lf S inv Col
-- statement:
--   The AAInv W construction uses the lf S inv Col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SubsetUpperHessenberg.lean#L223-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SubsetUpperHessenberg.lean#L223-L229

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

theorem AAInvW.lf_S_invCol (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hs : s ∈ Sset k r z) (a : Fin r) (i : Fin (2 * r + k + 1)) (hi : a.val ≤ i.val) :
    s⁻¹ i (eI k r a) = if i = eI k r a then 1 else 0 := by sorry
