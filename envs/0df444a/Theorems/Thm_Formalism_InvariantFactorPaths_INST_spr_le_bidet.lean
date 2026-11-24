-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_INST_spr_le_bidet
-- name    : Formalism.InvariantFactorPaths.INST.spr_le_bidet
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:36:21.850797+00:00
-- url     : https://prove2.me/theorems/9a18e0f8-3cc0-4d90-8a2d-8ea30d15f712
-- title:
--   INST: spr le bidet
-- statement:
--   The INST construction uses the spr le bidet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/Spread.lean#L66-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/Spread.lean#L66-L81

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

theorem Formalism.InvariantFactorPaths.INST.spr_le_bidet (R : Type*) [CommRing R] {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin n) (hI : ∀ k, Function.Injective (I k)) (lo : ℕ)
    (hlo : ∀ t : Fin n, lo ≤ shapeDeg sz t)
    (m : Fin n × Fin n →₀ ℕ) (hm : m ∈ (bideterminant R sz hsz I).support) (a : Fin n) : lo ≤ rowDeg m a := by sorry
