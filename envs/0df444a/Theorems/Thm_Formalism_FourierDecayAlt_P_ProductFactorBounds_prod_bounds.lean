-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ProductFactorBounds_prod_bounds
-- name    : Formalism.FourierDecayAlt.P.ProductFactorBounds.prod_bounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:08.631837+00:00
-- url     : https://prove2.me/theorems/dfd63275-e9e6-4b26-9332-558f605a51c0
-- title:
--   Product Factor Bounds: prod bounds
-- statement:
--   The Product Factor Bounds construction uses the prod bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ProductFactorBounds.lean#L35-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ProductFactorBounds.lean#L35-L48

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ProductFactorBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ProductFactorBounds
open Formalism.FourierDecayAlt.F7

theorem Formalism.FourierDecayAlt.P.ProductFactorBounds.prod_bounds (a b : ℝ) (ha1 : a ≤ 1) (hb : 0 ≤ b) (L : List ℝ)
    (h : ∀ f ∈ L, 1 - a ≤ f ∧ f ≤ 1 + b) :
    (1 - a) ^ L.length ≤ L.prod ∧ L.prod ≤ (1 + b) ^ L.length := by sorry
