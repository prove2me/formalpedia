-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PointSetConstantMembership_isPt_PT
-- name    : Formalism.FourierDecayAlt.P.PointSetConstantMembership.isPt_PT
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:49.406481+00:00
-- url     : https://prove2.me/theorems/9cb4d4f5-f705-4f0d-9179-b0b1ae0c3215
-- title:
--   Point Set Constant Membership: is Pt PT
-- statement:
--   The Point Set Constant Membership construction uses the is Pt PT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PointSetConstantMembership.lean#L51-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PointSetConstantMembership.lean#L51-L73

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointSetConstantMembership
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PointSetConstantMembership
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped InnerProductSpace ComplexConjugate

theorem Formalism.FourierDecayAlt.P.PointSetConstantMembership.isPt_PT {E : Type} [Field E] [DecidableEq E] (Sg : ℕ → ℕ → Finset E) (hNZ : NZSg Sg) :
    ∀ n p, p ∈ PT Sg n → IsPt n p := by sorry
