-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ldlat_linInd_base
-- name    : Formalism.GradedWeylDivisibility.ldlat_linInd_base
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:51.209356+00:00
-- url     : https://prove2.me/theorems/556b54d0-d884-441d-9a84-d0f7beb11444
-- title:
--   Graded Weyl Divisibility: ldlat lin Ind base
-- statement:
--   The Graded Weyl Divisibility construction uses the ldlat lin Ind base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LDlatLemmas.lean#L69-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LDlatLemmas.lean#L69-L86

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.ldlat_linInd_base {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K)) {σ ι : Type*} {b : ι → MvPolynomial σ R}
    (hb : LinearIndependent R b) : LinearIndependent K (fun i => map (algebraMap R K) (b i)) := by sorry
