-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FlagSpanVanishing_flagSpan_vanish
-- name    : Formalism.FourierDecayAlt.P.FlagSpanVanishing.flagSpan_vanish
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:27:37.377414+00:00
-- url     : https://prove2.me/theorems/ce835fd3-6d3d-483a-80a0-4f7e660c0400
-- title:
--   Flag Span Vanishing: flag Span vanish
-- statement:
--   The Flag Span Vanishing construction uses the flag Span vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FlagSpanVanishing.lean#L14-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FlagSpanVanishing.lean#L14-L25

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

theorem Formalism.FourierDecayAlt.P.FlagSpanVanishing.flagSpan_vanish (z : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)) (v : Fin (2 * r + k + 1) → ℂ)
    (hv : v ∈ C2.flagSpan k r z a) (i : Fin (2 * r + k + 1)) (hi : a.val ≤ i.val) : v i = 0 := by sorry
