-- Prove2me | Theorems.Thm_AAInvW_grouping
-- name    : AAInvW.grouping
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:27:11.400038+00:00
-- url     : https://prove2.me/theorems/08c5fef3-444c-445f-9aab-d14a61c2247e
-- title:
--   AAInv W: grouping
-- statement:
--   The AAInv W construction uses the grouping property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/CauchyBinet.lean#L57-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/CauchyBinet.lean#L57-L128

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

theorem AAInvW.grouping {A : Type*} [Ring A] [Algebra ℂ A] {t N : ℕ} (κ : Fin N → ℕ) (hκ : Function.Injective κ)
    (F : (Fin t → Fin N) → A)
    (hF : ∀ (d : Fin t → Fin N) (τ : Equiv.Perm (Fin t)),
      F (d ∘ τ) = ((Equiv.Perm.sign τ : ℤ) : A) * F d)
    (hF0 : ∀ d : Fin t → Fin N, ¬ Function.Injective d → F d = 0) (W : (Fin t → Fin N) → ℂ) :
    ∑ d, W d • F d = ∑ C : Fin t → Fin N,
      if StrictMono (fun l => κ (C l)) then
        (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * W (C ∘ σ)) • F C else 0 := by sorry
