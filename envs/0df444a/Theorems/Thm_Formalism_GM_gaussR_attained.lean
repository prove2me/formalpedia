-- Prove2me | Theorems.Thm_Formalism_GM_gaussR_attained
-- name    : Formalism.GM.gaussR_attained
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:45.189818+00:00
-- url     : https://prove2.me/theorems/2826e0a4-923a-4fad-bc0b-edb86af1b36b
-- title:
--   GM: gauss R attained
-- statement:
--   The GM construction uses the gauss R attained property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GaussRad.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GaussRad.lean#L21-L25

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

theorem Formalism.GM.gaussR_attained (ρ : NNReal) (P : K[X]) (hP : P ≠ 0) :
    ∃ k, ‖P.coeff k‖₊ * ρ ^ k = gaussR ρ P := by sorry
