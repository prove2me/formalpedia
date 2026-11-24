-- Prove2me | Theorems.Thm_Formalism_L2_DIV_fockL_apply
-- name    : Formalism.L2.DIV.fockL_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:24.347704+00:00
-- url     : https://prove2.me/theorems/78500ae3-0f8a-4730-bb23-84e6a5978e91
-- title:
--   DIV: fock L apply
-- statement:
--   The DIV construction uses the fock L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefMod.lean#L55-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefMod.lean#L55-L55

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_LocalRingCardinality_DataCoeff
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] [StarRing K] {σ : Type}

theorem Formalism.L2.DIV.fockL_apply (f g : MvPolynomial σ K) : fockL f g = fockS f g := by sorry
