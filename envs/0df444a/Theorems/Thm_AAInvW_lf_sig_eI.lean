-- Prove2me | Theorems.Thm_AAInvW_lf_sig_eI
-- name    : AAInvW.lf_sig_eI
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:45:58.587712+00:00
-- url     : https://prove2.me/theorems/4e87df3d-d3b4-49a0-858d-14748332533d
-- title:
--   AAInv W: lf sig e I
-- statement:
--   The AAInv W construction uses the lf sig e I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SubsetUpperHessenberg.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SubsetUpperHessenberg.lean#L18-L22

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

theorem AAInvW.lf_sig_eI (k r : ℕ) (a : Fin r) : hkSig k r (eI k r a) = esI k r a := by sorry
