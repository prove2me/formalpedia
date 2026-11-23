-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PointSetConstantMembership_norm_sq_comb
-- name    : Formalism.FourierDecayAlt.P.PointSetConstantMembership.norm_sq_comb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:46.266869+00:00
-- url     : https://prove2.me/theorems/39b196a4-4fb9-446c-9996-5d2fc82dfdc1
-- title:
--   Point Set Constant Membership: norm sq comb
-- statement:
--   The Point Set Constant Membership construction uses the norm sq comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PointSetConstantMembership.lean#L37-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PointSetConstantMembership.lean#L37-L49

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

theorem Formalism.FourierDecayAlt.P.PointSetConstantMembership.norm_sq_comb {α : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : Finset α) (c : α → ℂ) (V : α → H) :
    ((‖∑ p ∈ P, c p • V p‖ ^ 2 : ℝ) : ℂ)
      = ∑ p ∈ P, ∑ p' ∈ P, (conj (c p) * c p') * ⟪V p, V p'⟫_ℂ := by sorry
