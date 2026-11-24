-- Prove2me | Theorems.Thm_Formalism_riemannHypothesis_of_zero_free_halfPlane
-- name    : Formalism.riemannHypothesis_of_zero_free_halfPlane
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:45:16.520711+00:00
-- url     : https://prove2.me/theorems/708c3b92-6adb-4967-9e3b-1b52aeb00579
-- title:
--   Formalism: riemann Hypothesis of zero free half Plane
-- statement:
--   The Formalism construction uses the riemann Hypothesis of zero free half Plane property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/RHofHalfPlane.lean#L44-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/RHofHalfPlane.lean#L44-L59

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_RHofHalfPlane
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism

theorem Formalism.riemannHypothesis_of_zero_free_halfPlane : RHofHalfPlane := by sorry
