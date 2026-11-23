-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx12_lift_per
-- name    : Formalism.FourierDecayAlt.P.Jx12.lift_per
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:57.13772+00:00
-- url     : https://prove2.me/theorems/7e8a2f70-ebe1-4134-87ce-805bcd3c373c
-- title:
--   Jx12: lift per
-- statement:
--   The Jx12 construction uses the lift per property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PullLatticeTypedUnit.lean#L28-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PullLatticeTypedUnit.lean#L28-L44

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AxiomsFromFamilies
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevToThreshold
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx12

theorem Formalism.FourierDecayAlt.P.Jx12.lift_per (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (hg : 0 < g) (ν : ℤ) (s : ℕ)
    (y : E) : y ∈ S6.liftLat E g ν s ↔ (g : E) ^ 2 * y ∈ S6.perLat E g (-ν) s := by sorry
