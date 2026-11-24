-- Prove2me | Theorems.Thm_Formalism_L2_G_Triv_bc_injective
-- name    : Formalism.L2.G.Triv.bc_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:32.660869+00:00
-- url     : https://prove2.me/theorems/5ee2d46a-0592-43f2-a567-02e7fa167e15
-- title:
--   Triv: bc injective
-- statement:
--   The Triv construction uses the bc injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/TrivialTransfer/OneAddPowOfSq.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/TrivialTransfer/OneAddPowOfSq.lean#L19-L24

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

theorem Formalism.L2.G.Triv.bc_injective {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n] (φ : A →+* B)
    (hφ : Function.Injective φ) : Function.Injective (bc (n := n) φ) := by sorry
