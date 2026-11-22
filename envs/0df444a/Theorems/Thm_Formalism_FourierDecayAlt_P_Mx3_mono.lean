-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_mono
-- name    : Formalism.FourierDecayAlt.P.Mx3.mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:46:10.602579+00:00
-- url     : https://prove2.me/theorems/a28f728c-22b0-48a2-b911-929460457fed
-- title:
--   Mx3: mono
-- statement:
--   The Mx3 construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InterlaceSignTwo.lean#L38-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InterlaceSignTwo.lean#L38-L49

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx3

theorem Formalism.FourierDecayAlt.P.Mx3.mono (k : ℕ) (u u' ρ : ℕ → ℝ) (h : I.Interlaces k u u' ρ) :
    ∀ d i, 1 ≤ i → i + d ≤ k → u (i + d) ≤ u i ∧ u' (i + d) ≤ u' i := by sorry
