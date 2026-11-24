-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_finite_between
-- name    : Formalism.HermitianLatticesTheory.classSetAssembly_finite_between
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:38.483717+00:00
-- url     : https://prove2.me/theorems/833065f6-32ad-4190-8223-4e7f752ccb7a
-- title:
--   Hermitian Lattices Theory: class Set Assembly finite between
-- statement:
--   The Hermitian Lattices Theory construction uses the class Set Assembly finite between property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L343-L387
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L343-L387

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

theorem Formalism.HermitianLatticesTheory.classSetAssembly_finite_between (hE : FinIntermediate) {K W : Type} [Field K] [CharZero K]
    [AddCommGroup W] [Module K W] {n : ℕ} (u : Fin n → W) (e : ℤ) (he : e ≠ 0) :
    {M : AddSubgroup W | AddSubgroup.closure (Set.range u) ≤ M ∧
      M ≤ AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i)}.Finite := by sorry
