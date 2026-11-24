-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_closure_range_le_closure_range_inv_smul
-- name    : Formalism.HermitianLatticesTheory.closure_range_le_closure_range_inv_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:32.486363+00:00
-- url     : https://prove2.me/theorems/588dc912-a0c4-4f96-bed9-048eb9883c14
-- title:
--   Hermitian Lattices Theory: closure range le closure range inv smul
-- statement:
--   The Hermitian Lattices Theory construction uses the closure range le closure range inv smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L310-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L310-L322

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {V : Type*} [AddCommGroup V]

theorem Formalism.HermitianLatticesTheory.closure_range_le_closure_range_inv_smul {K : Type*} [Field K] [CharZero K] [Module K V] {n : ℕ} (u : Fin n → V)
    (e : ℤ) (he : e ≠ 0) :
    AddSubgroup.closure (Set.range u) ≤
      AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i) := by sorry
