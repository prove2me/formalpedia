-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OneLevelCoefficients_small
-- name    : Formalism.FourierDecayAlt.P.OneLevelCoefficients.small
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:54.671026+00:00
-- url     : https://prove2.me/theorems/b20ce929-1e54-4d58-99b7-44989e5f166e
-- title:
--   One Level Coefficients: small
-- statement:
--   The One Level Coefficients construction uses the small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OneLevelCoefficients.lean#L206-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OneLevelCoefficients.lean#L206-L209

import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelCoefficients
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OneLevelCoefficients
open Formalism.FourierDecayAlt.TB Finset
open scoped ComplexOrder
variable {E W : Type} [Field E]

theorem Formalism.FourierDecayAlt.P.OneLevelCoefficients.small (r f : ℕ) (C C₀ Θ : ℝ) (hΘ : 0 < Θ) (h0 : 0 ≤ C₀) (h : C₀ ≤ C)
    (hs : (r : ℝ) * (C / Θ) ^ f ≤ 1) : (r : ℝ) * (C₀ / Θ) ^ f ≤ 1 := by sorry
