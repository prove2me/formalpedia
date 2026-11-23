-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PointSetConstantMembership_bound_PT
-- name    : Formalism.FourierDecayAlt.P.PointSetConstantMembership.bound_PT
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:41.478319+00:00
-- url     : https://prove2.me/theorems/7e4e90fd-c9ea-4638-9073-45178f05c23b
-- title:
--   Point Set Constant Membership: bound PT
-- statement:
--   The Point Set Constant Membership construction uses the bound PT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PointSetConstantMembership.lean#L99-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PointSetConstantMembership.lean#L99-L116

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

theorem Formalism.FourierDecayAlt.P.PointSetConstantMembership.bound_PT {E : Type} [Field E] [DecidableEq E] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (Kn : Pt E → Pt E → ℂ) (V : Pt E → H) {ρ : Type}
    (c : ρ → Pt E → ℂ) (P : Finset (Pt E)) (R : Finset ρ)
    (h : PSDOn P (fun p p' => Kn p p' - ∑ x ∈ R, conj (c x p) * c x p')) :
    ∑ x ∈ R, ‖∑ p ∈ P, c x p • V p‖ ^ 2 ≤ (gram Kn V P).re := by sorry
