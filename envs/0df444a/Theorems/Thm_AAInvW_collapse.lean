-- Prove2me | Theorems.Thm_AAInvW_collapse
-- name    : AAInvW.collapse
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:27:57.246846+00:00
-- url     : https://prove2.me/theorems/6d09a3c7-54be-423c-bf32-58c353ae9e89
-- title:
--   AAInv W: collapse
-- statement:
--   The AAInv W construction uses the collapse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/CauchyBinet.lean#L9-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/CauchyBinet.lean#L9-L55

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CauchyBinet
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

theorem AAInvW.collapse {A : Type*} [AddCommGroup A] [Module ℂ A] {N r m : ℕ} (hm : m ≤ r)
    (φ : Fin r → Fin N) (hφ : Function.Injective φ) (w : Fin N → Fin N → ℂ)
    (hw : ∀ (a : Fin r) (i : Fin N), (∀ b : Fin r, b.val < a.val → i ≠ φ b) →
      w i (φ a) = if i = φ a then 1 else 0)
    (q : (Fin m → Fin N) → A) (hq : ∀ c : Fin m → Fin N, ¬ Function.Injective c → q c = 0) :
    ∑ c : Fin m → Fin N, (∏ j, w (c j) (φ (Fin.castLE hm j))) • q c =
      q (fun j => φ (Fin.castLE hm j)) := by sorry
