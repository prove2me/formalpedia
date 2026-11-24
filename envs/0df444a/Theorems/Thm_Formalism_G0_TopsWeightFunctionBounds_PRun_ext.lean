-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_PRun_ext
-- name    : Formalism.G0.TopsWeightFunctionBounds.PRun_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:21.22893+00:00
-- url     : https://prove2.me/theorems/1e5e4945-ab13-4ac6-b5c6-4e92834e1838
-- title:
--   Tops Weight Function Bounds: PRun ext
-- statement:
--   The Tops Weight Function Bounds construction uses the PRun ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L575-L639
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L575-L639

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds

theorem Formalism.G0.TopsWeightFunctionBounds.PRun_ext {n : ℕ} (hn : Even n) {T : Finset ℕ} {L₂ b j t d : ℕ} {ev : Bool} {u : Fin j → ℕ}
    (hu : PRun n T L₂ b j t d u) (hd : d ≤ t) (hev : ev = decide (Even (b + t)))
    (hnone : ∀ x, t - d < x → x ≤ t → (b + x) % n ∉ T)
    (hT : (b + (t + 1)) % n ∈ T) (hok : okG L₂ j d ev = true) :
    PRun n T L₂ b (j + 1) (t + 1) 0 (snocF u (t + 1)) := by sorry
