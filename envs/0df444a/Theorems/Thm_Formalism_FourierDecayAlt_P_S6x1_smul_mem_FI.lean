-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x1_smul_mem_FI
-- name    : Formalism.FourierDecayAlt.P.S6x1.smul_mem_FI
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:16:03.87834+00:00
-- url     : https://prove2.me/theorems/bda39f79-0acf-4b85-bb19-dc79e7f6dd7c
-- title:
--   S6x1: smul mem FI
-- statement:
--   The S6x1 construction uses the smul mem FI property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PeriodLatticeFactsSplitOfGeneral.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PeriodLatticeFactsSplitOfGeneral.lean#L26-L31

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x1
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors

theorem Formalism.FourierDecayAlt.P.S6x1.smul_mem_FI (E : Type) [Field E] [NumberField E] [IsCMField E] (A : FI E)
    (a : 𝓞 (maximalRealSubfield E)) (t : E) (ht : t ∈ A) :
    algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ A := by sorry
