-- Prove2me | Theorems.Thm_AAInvW_lf_N_rowStar
-- name    : AAInvW.lf_N_rowStar
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:54:50.90495+00:00
-- url     : https://prove2.me/theorems/6e531845-76ec-4943-86f2-29be75595502
-- title:
--   AAInv W: lf N row Star
-- statement:
--   The AAInv W construction uses the lf N row Star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SubsetUpperHessenberg.lean#L115-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SubsetUpperHessenberg.lean#L115-L139

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

theorem AAInvW.lf_N_rowStar (k r : ℕ) {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hm : m ∈ Formalism.QuantumDeterminants.Nset k r) : ∀ (b : ℕ) (hb : b < r) (p : Fin (2 * r + k + 1)), p.val ≤ 2 * r + k - b →
      m (esI k r ⟨b, hb⟩) p = if p = esI k r ⟨b, hb⟩ then 1 else 0 := by sorry
