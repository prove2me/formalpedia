-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx12_mem_idl_shift
-- name    : Formalism.FourierDecayAlt.P.Jx12.mem_idl_shift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:01.4634+00:00
-- url     : https://prove2.me/theorems/ba049a76-f1be-4f4e-b899-4a435bac19f6
-- title:
--   Jx12: mem idl shift
-- statement:
--   The Jx12 construction uses the mem idl shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PullLatticeTypedUnit.lean#L12-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PullLatticeTypedUnit.lean#L12-L26

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

theorem Formalism.FourierDecayAlt.P.Jx12.mem_idl_shift (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (hg : 0 < g) (k ν : ℤ)
    (y : E) : y ∈ S6.zsub E (S6.idl E g k ν) ↔ (g : E) ^ 2 * y ∈ S6.zsub E (S6.idl E g (k + 2) ν) := by sorry
