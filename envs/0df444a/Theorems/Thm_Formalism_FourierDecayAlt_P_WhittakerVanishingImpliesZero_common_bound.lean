-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_common_bound
-- name    : Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.common_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:33.693926+00:00
-- url     : https://prove2.me/theorems/24bffc32-8a2e-43a5-baa2-745eee058a29
-- title:
--   Whittaker Vanishing Implies Zero: common bound
-- statement:
--   The Whittaker Vanishing Implies Zero construction uses the common bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WhittakerVanishingImpliesZero.lean#L75-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WhittakerVanishingImpliesZero.lean#L75-L82

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
open Formalism.FourierDecayAlt.G

theorem Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.common_bound {α : Type*} (k : ℕ) (f : ℕ → α → ℝ) (h : ∀ j, ∃ C : ℝ, ∀ a, f j a ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ k, ∀ a, f j a ≤ C := by sorry
