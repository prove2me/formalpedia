-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FlagSpanVanishing_sig_notW
-- name    : Formalism.FourierDecayAlt.P.FlagSpanVanishing.sig_notW
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:27:07.678958+00:00
-- url     : https://prove2.me/theorems/71f08aec-3f90-480b-8bd8-531fae473c03
-- title:
--   Flag Span Vanishing: sig not W
-- statement:
--   The Flag Span Vanishing construction uses the sig not W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FlagSpanVanishing.lean#L75-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FlagSpanVanishing.lean#L75-L79

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LinearChangeOfVariablesBis
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagSpanVanishing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FlagSpanVanishing
open C2x5 C2x7
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.FlagSpanVanishing.sig_notW (x : Fin (2 * r + k + 1)) (hx : ¬ (r ≤ x.val ∧ x.val ≤ r + k)) :
    ¬ (r ≤ (GBasic.sig k r x).val ∧ (GBasic.sig k r x).val ≤ r + k) := by sorry
