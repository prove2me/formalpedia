-- Prove2me | Theorems.Thm_Formalism_L2_G_Triv_unip_coprime
-- name    : Formalism.L2.G.Triv.unip_coprime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:36.821729+00:00
-- url     : https://prove2.me/theorems/1d3a6e5d-2293-4431-869f-ef244271a340
-- title:
--   Triv: unip coprime
-- statement:
--   The Triv construction uses the unip coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/TrivialTransfer/OneAddPowOfSq.lean#L133-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/TrivialTransfer/OneAddPowOfSq.lean#L133-L140

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

theorem Formalism.L2.G.Triv.unip_coprime (I : Ideal R) (hinf : (⨅ m : ℕ, I ^ m) = ⊥) (g : ℕ) (hg : g.Prime) (hgI : (g : R) ∈ I)
    (A : Matrix (Fin k) (Fin k) R) (hA : ∀ i j, j ≤ i → (A - 1) i j ∈ I) (N : ℕ) (hN : IsUnit (N : R))
    (hc : Nat.Coprime N g) (hAN : A ^ N = 1) : A = 1 := by sorry
