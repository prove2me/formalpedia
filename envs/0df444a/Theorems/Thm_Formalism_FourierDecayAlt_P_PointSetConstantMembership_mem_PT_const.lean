-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PointSetConstantMembership_mem_PT_const
-- name    : Formalism.FourierDecayAlt.P.PointSetConstantMembership.mem_PT_const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:47.523047+00:00
-- url     : https://prove2.me/theorems/510fd716-7920-45fc-b2fd-58ee7ef18495
-- title:
--   Point Set Constant Membership: mem PT const
-- statement:
--   The Point Set Constant Membership construction uses the mem PT const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PointSetConstantMembership.lean#L75-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PointSetConstantMembership.lean#L75-L97

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

theorem Formalism.FourierDecayAlt.P.PointSetConstantMembership.mem_PT_const {E : Type} [Field E] [DecidableEq E] (T : Finset E) (p : Pt E) :
    ∀ n, IsPt n p → (∀ b ∈ p, b.2 ∈ T) → p ∈ PT (fun _ _ => T) n := by sorry
