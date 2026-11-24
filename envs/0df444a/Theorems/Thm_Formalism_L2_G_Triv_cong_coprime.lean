-- Prove2me | Theorems.Thm_Formalism_L2_G_Triv_cong_coprime
-- name    : Formalism.L2.G.Triv.cong_coprime
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:40.860585+00:00
-- url     : https://prove2.me/theorems/74259931-1211-4d0a-a7df-2e1ffee069d1
-- title:
--   Triv: cong coprime
-- statement:
--   The Triv construction uses the cong coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/TrivialTransfer/OneAddPowOfSq.lean#L86-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/TrivialTransfer/OneAddPowOfSq.lean#L86-L131

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ClosureUpperUni
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddPowOfMulSelfEqZero
import Definitions.Def_Lemmata_GeneralBFactLeftTail_Imports
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_OneAddPowOfSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Triv
variable {R : Type} [CommRing R] {k : ℕ}

theorem Formalism.L2.G.Triv.cong_coprime (I : Ideal R) (hinf : (⨅ m : ℕ, I ^ m) = ⊥) (B : Matrix (Fin k) (Fin k) R)
    (hB : ∀ i j, (B - 1) i j ∈ I) (N : ℕ) (hN : IsUnit (N : R)) (hBN : B ^ N = 1) : B = 1 := by sorry
