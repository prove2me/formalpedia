-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Interlace_antitone_on
-- name    : Formalism.FourierDecayAlt.P.Interlace.antitone_on
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:51:25.649796+00:00
-- url     : https://prove2.me/theorems/3216cb0e-c128-4420-9094-f03b435a8cb8
-- title:
--   Interlace: antitone on
-- statement:
--   The Interlace construction uses the antitone on property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Interlace.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Interlace.lean#L13-L18

import Definitions.Def_Formalism_HermitianCurvature_StatementI
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Interlace
open Finset Formalism.FourierDecayAlt.I

theorem Formalism.FourierDecayAlt.P.Interlace.antitone_on {f : ℕ → ℝ} {k : ℕ} (h : ∀ i, 1 ≤ i → i + 1 ≤ k → f (i + 1) ≤ f i) :
    ∀ i j, 1 ≤ i → i ≤ j → j ≤ k → f j ≤ f i := by sorry
