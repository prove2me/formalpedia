-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrderIndexAndStrata_mid_form
-- name    : Formalism.FourierDecayAlt.P.OrderIndexAndStrata.mid_form
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:01:08.861534+00:00
-- url     : https://prove2.me/theorems/0fe8fd95-2a18-4f52-bd84-7b3a92071f5d
-- title:
--   Order Index And Strata: mid form
-- statement:
--   The Order Index And Strata construction uses the mid form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrderIndexAndStrata.lean#L148-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrderIndexAndStrata.lean#L148-L160

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderIndexAndStrata
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrderIndexAndStrata
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni)
open Formalism.FourierDecayAlt.S3

theorem Formalism.FourierDecayAlt.P.OrderIndexAndStrata.mid_form {A : Type} [CommRing A] {k : ℕ} (y : Matrix (Mid k) (Mid k) A) (hy : IsUnit y.det)
    (c22 : ∀ a, y a (Sum.inr ()) = if a = Sum.inr () then 1 else 0)
    (r22 : ∀ b, y (Sum.inr ()) b = if b = Sum.inr () then 1 else 0) :
    ∃ h, IsUnit h.det ∧ y = midEmb h := by sorry
