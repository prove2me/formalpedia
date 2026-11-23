-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PointSetConstantMembership_gram_nonneg
-- name    : Formalism.FourierDecayAlt.P.PointSetConstantMembership.gram_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:31:14.311602+00:00
-- url     : https://prove2.me/theorems/f8d74353-d827-4013-a6de-1694b8b8a0df
-- title:
--   Point Set Constant Membership: gram nonneg
-- statement:
--   The Point Set Constant Membership construction uses the gram nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PointSetConstantMembership.lean#L8-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PointSetConstantMembership.lean#L8-L35

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

theorem Formalism.FourierDecayAlt.P.PointSetConstantMembership.gram_nonneg {α : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : Finset α) (k : α → α → ℂ) (V : α → H)
    (hk : ∀ a : α → ℂ, 0 ≤ (∑ x ∈ P, ∑ y ∈ P, conj (a x) * k x y * a y).re) :
    0 ≤ (∑ p ∈ P, ∑ p' ∈ P, k p p' * ⟪V p, V p'⟫_ℂ).re := by sorry
