-- Prove2me | Theorems.Thm_Formalism_GM_M_FB_hom_XX
-- name    : Formalism.GM.M.FB.hom_XX
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:16:10.5165+00:00
-- url     : https://prove2.me/theorems/08ec227c-63bb-489a-b1e7-36eca2ed585d
-- title:
--   FB: hom XX
-- statement:
--   The FB construction uses the hom XX property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L201-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L201-L205

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.FB
open MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.GM.M.FB.hom_XX (u v : Fin (N + 1) × Fin r) (h : wL N r u + wL N r v = 1) :
    IsWeightedHomogeneous (wL N r) (X u * X v : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) 1 := by sorry
