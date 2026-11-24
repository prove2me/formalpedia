-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gf_det_mem
-- name    : Formalism.HermitianLatticeCounting.P.gf_det_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:52.471115+00:00
-- url     : https://prove2.me/theorems/54bea2cf-892e-44cc-84be-cd095b28ee0e
-- title:
--   P: gf det mem
-- statement:
--   The P construction uses the gf det mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L468-L475
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L468-L475

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix

theorem Formalism.HermitianLatticeCounting.P.gf_det_mem {K : Type*} [Field K] (O : Subring K) {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (h : ∀ i j, A i j ∈ O) : A.det ∈ O := by sorry
