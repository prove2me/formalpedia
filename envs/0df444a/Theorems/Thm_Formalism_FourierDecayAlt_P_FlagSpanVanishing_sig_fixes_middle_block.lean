-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FlagSpanVanishing_sig_fixes_middle_block
-- name    : Formalism.FourierDecayAlt.P.FlagSpanVanishing.sig_fixes_middle_block
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:26:50.883059+00:00
-- url     : https://prove2.me/theorems/84e08990-e57b-4838-83bb-3eb9f427bb72
-- title:
--   Flag Span Vanishing: sig fixes middle block
-- statement:
--   The Flag Span Vanishing construction uses the sig fixes middle block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FlagSpanVanishing.lean#L81-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FlagSpanVanishing.lean#L81-L82

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

theorem Formalism.FourierDecayAlt.P.FlagSpanVanishing.sig_fixes_middle_block (x : Fin (2 * r + k + 1)) (hx : r ≤ x.val ∧ x.val ≤ r + k) : GBasic.sig k r x = x := by sorry
