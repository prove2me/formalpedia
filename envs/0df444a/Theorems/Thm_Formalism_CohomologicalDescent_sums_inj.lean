-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_sums_inj
-- name    : Formalism.CohomologicalDescent.sums_inj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:35:43.736821+00:00
-- url     : https://prove2.me/theorems/600c6883-0e68-4ee1-b4f1-05807a52356a
-- title:
--   Cohomological Descent: sums inj
-- statement:
--   The Cohomological Descent construction uses the sums inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SharperSizeNeedsMleKFalse.lean#L31-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SharperSizeNeedsMleKFalse.lean#L31-L53

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
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
open Formalism Formalism.CohomologicalDescent
open Classical

theorem Formalism.CohomologicalDescent.sums_inj (D h : ℕ) (L : ℝ) (hD : 1 ≤ D) (hDh : D ≤ h) (hh : (h : ℝ) < L ^ 2)
    (hL : 1 ≤ L) (l l' : ℕ) (hl : l.Prime) (hl' : l'.Prime) (hLl : L < (l : ℝ))
    (hLl' : L < (l' : ℝ)) (hg : ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ))
    (heq : d0 l (D : ℤ) = d0 l' (D : ℤ)) : l = l' := by sorry
