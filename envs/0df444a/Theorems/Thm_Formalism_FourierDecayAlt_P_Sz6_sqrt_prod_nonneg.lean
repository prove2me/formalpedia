-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz6_sqrt_prod_nonneg
-- name    : Formalism.FourierDecayAlt.P.Sz6.sqrt_prod_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:37:03.468008+00:00
-- url     : https://prove2.me/theorems/183a8244-0f47-4d96-a646-bc3604d3937b
-- title:
--   Sz6: sqrt prod nonneg
-- statement:
--   The Sz6 construction uses the sqrt prod nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaFactorisation.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaFactorisation.lean#L9-L16

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaFactorisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.Sz Finset
open Formalism.FourierDecayAlt.P.Sz6

theorem Formalism.FourierDecayAlt.P.Sz6.sqrt_prod_nonneg {α : Type} (s : Finset α) (f : α → ℝ) (h : ∀ i ∈ s, 0 ≤ f i) :
    Real.sqrt (∏ i ∈ s, f i) = ∏ i ∈ s, Real.sqrt (f i) := by sorry
