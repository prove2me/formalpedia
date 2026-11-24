-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FlagSpanVanishing_wpart_uh
-- name    : Formalism.FourierDecayAlt.P.FlagSpanVanishing.wpart_uh
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:27:17.974816+00:00
-- url     : https://prove2.me/theorems/b5da9742-e578-45a3-a243-3d0d21cf9ba4
-- title:
--   Flag Span Vanishing: wpart uh
-- statement:
--   The Flag Span Vanishing construction uses the wpart uh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FlagSpanVanishing.lean#L84-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FlagSpanVanishing.lean#L84-L138

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

theorem Formalism.FourierDecayAlt.P.FlagSpanVanishing.wpart_uh (s : B.Mat k r) (hs : s ∈ B.GV k r)
    (hA : ∀ p j : Fin (2 * r + k + 1), r + k < p.val → r ≤ j.val → j.val ≤ r + k → s p j = 0) :
    wpart s ∈ UH (Hpk k r) := by sorry
