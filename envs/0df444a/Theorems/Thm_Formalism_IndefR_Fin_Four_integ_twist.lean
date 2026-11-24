-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_integ_twist
-- name    : Formalism.IndefR.Fin.Four.integ_twist
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:27.884911+00:00
-- url     : https://prove2.me/theorems/82f0fefa-623a-4b61-be96-093dc6466fec
-- title:
--   Four: integ twist
-- statement:
--   The Four construction uses the integ twist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean#L190-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean#L190-L197

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasC_Imports
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Finset
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W : Type*} [AddCommGroup W]
variable {H : AddSubgroup W} (hfin : ∀ k, 0 < k → Finite (Qt k H))
include hfin

theorem Formalism.IndefR.Fin.Four.integ_twist {k : ℕ} (hk : 0 < k) {g : W → ℂ} (hg : IsInv k H g) {v : W} (hv : v ∈ H) {ζ : ℂ}
    (hζ : ζ ≠ 1) (htw : ∀ t ∈ H, g (t + v) = ζ * g t) : integ H g = 0 := by sorry
