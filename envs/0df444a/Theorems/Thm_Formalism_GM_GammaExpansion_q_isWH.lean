-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_q_isWH
-- name    : Formalism.GM.GammaExpansion.q_isWH
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:49.7749+00:00
-- url     : https://prove2.me/theorems/a2827063-81a8-40bb-9517-47e9d21ebb82
-- title:
--   Gamma Expansion: q is WH
-- statement:
--   The Gamma Expansion construction uses the q is WH property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L911-L959
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L911-L959

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open MvPolynomial Finset
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}

theorem Formalism.GM.GammaExpansion.q_isWH (LL : M.Letters (N + 1)) (ρ : Fin r) (e : ℕ) (h : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p])
    (hh : h ∈ M.Pol p r (lowerLast LL e)) (g : Fin (N + 1 + 1) → ℕ) :
    IsWeightedHomogeneous (fun y : Fin (N + 1 + 1) × Fin r => g y.1) (aeval (M.freezeSub p LL ρ) h)
      (∑ b, (g (Fin.castSucc b) + g (Fin.last (N + 1))) * (lowerLast LL e).deg b) := by sorry
