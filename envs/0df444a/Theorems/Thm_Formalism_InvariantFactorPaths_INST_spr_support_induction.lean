-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_INST_spr_support_induction
-- name    : Formalism.InvariantFactorPaths.INST.spr_support_induction
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:40:34.548218+00:00
-- url     : https://prove2.me/theorems/aff84975-5366-441a-a4d0-714a380ca598
-- title:
--   INST: spr support induction
-- statement:
--   The INST construction uses the spr support induction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/Spread.lean#L83-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/Spread.lean#L83-L105

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDrowLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Spread
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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.INST
open Formalism.GradedWeylDivisibility

theorem Formalism.InvariantFactorPaths.INST.spr_support_induction (R : Type) [CommRing R] [IsDomain R] (r n : ℕ) (ν : Fin n → ℕ)
    (P : (Fin r × Fin n →₀ ℕ) → Prop)
    (hP : ∀ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ i, sz i ≤ n) (I : ∀ i, Fin (sz i) → Fin r),
      shapeDeg sz = ν → (∀ i, StrictMono (I i)) → ∀ m ∈ (bideterminant R sz hsz I).support, P m)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ dualWeyl R r n ν) : ∀ m ∈ f.support, P m := by sorry
