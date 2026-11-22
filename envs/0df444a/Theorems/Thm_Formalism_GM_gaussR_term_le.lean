-- Prove2me | Theorems.Thm_Formalism_GM_gaussR_term_le
-- name    : Formalism.GM.gaussR_term_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:02:15.975605+00:00
-- url     : https://prove2.me/theorems/75eb38f2-4266-46af-9da0-25f9c0427af8
-- title:
--   GM: gauss R term le
-- statement:
--   The GM construction uses the gauss R term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GaussRad.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GaussRad.lean#L11-L16

import Definitions.Def_Formalism_MahlerMeasure_StatementD
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GaussRad
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset Polynomial
variable {K : Type} [NormedField K]

theorem Formalism.GM.gaussR_term_le (ρ : NNReal) (P : K[X]) (k : ℕ) :
    ‖P.coeff k‖₊ * ρ ^ k ≤ gaussR ρ P := by sorry
