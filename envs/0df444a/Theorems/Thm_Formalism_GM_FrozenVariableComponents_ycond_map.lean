-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_ycond_map
-- name    : Formalism.GM.FrozenVariableComponents.ycond_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:32.495806+00:00
-- url     : https://prove2.me/theorems/04aecab6-32ea-42f7-800b-9329a6d3c223
-- title:
--   Frozen Variable Components: ycond map
-- statement:
--   The Frozen Variable Components construction uses the ycond map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L314-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L314-L338

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
variable [NeZero r]

theorem Formalism.GM.FrozenVariableComponents.ycond_map {NA NB : ℕ} (LA : Letters NA) (LB : Letters NB) (jA jB : ℕ) (M : WithTop ℤ)
    (P : MvPolynomial (Fin NA × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin NB × Fin r) ℚ_[p])
    (hc : ∀ c d F, P (glAct p LA jA c d F) = glAct p LB jB c d (P F))
    (hs : ∀ F, ∀ m ∈ (P F).support, ∃ m0 ∈ F.support, wt LB jB 0 m = wt LA jA 0 m0) :
    ∀ F ∈ YCond p LA jA M, P F ∈ YCond p LB jB M := by sorry
