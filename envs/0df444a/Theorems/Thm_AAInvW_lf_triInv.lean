-- Prove2me | Theorems.Thm_AAInvW_lf_triInv
-- name    : AAInvW.lf_triInv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:54:49.557006+00:00
-- url     : https://prove2.me/theorems/c20b919a-dfde-4cb5-b483-9030e08459dc
-- title:
--   AAInv W: lf tri Inv
-- statement:
--   The AAInv W construction uses the lf tri Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SubsetUpperHessenberg.lean#L195-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SubsetUpperHessenberg.lean#L195-L221

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

theorem AAInvW.lf_triInv (k r : ℕ) (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hM : M⁻¹ * M = 1)
    (hU : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val → M i (eI k r a) = if i = eI k r a then 1 else 0) :
    ∀ (a : ℕ) (ha : a < r) (i : Fin (2 * r + k + 1)), a ≤ i.val →
      M⁻¹ i (eI k r ⟨a, ha⟩) = if i = eI k r ⟨a, ha⟩ then 1 else 0 := by sorry
