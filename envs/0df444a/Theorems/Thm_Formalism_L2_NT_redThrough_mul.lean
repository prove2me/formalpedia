-- Prove2me | Theorems.Thm_Formalism_L2_NT_redThrough_mul
-- name    : Formalism.L2.NT.redThrough_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:55:44.680812+00:00
-- url     : https://prove2.me/theorems/ac8e3b96-0c68-44f0-b8bc-5338ac1322f2
-- title:
--   NT: red Through mul
-- statement:
--   The NT construction uses the red Through mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/TypesDefs.lean#L111-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/TypesDefs.lean#L111-L115

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial
open Formalism Formalism.L2 Formalism.L2.NT
open Formalism.L2.Host
variable {Ω : Type} [Field Ω]
variable (B : ValuationSubring Ω) {l : ℕ} [Fact l.Prime] (κ : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar l)

theorem Formalism.L2.NT.redThrough_mul {z w : Ω} (hz : z ∈ B) (hw : w ∈ B) :
    redThrough B κ (z * w) = redThrough B κ z * redThrough B κ w := by sorry
