-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_torsion
-- name    : Formalism.HermitianLatticesTheory.classSetAssembly_torsion
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:19.277248+00:00
-- url     : https://prove2.me/theorems/f78fa6d7-4c14-49af-8c75-52673a4c5d24
-- title:
--   Hermitian Lattices Theory: class Set Assembly torsion
-- statement:
--   The Hermitian Lattices Theory construction uses the class Set Assembly torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L273-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L273-L285

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

theorem Formalism.HermitianLatticesTheory.classSetAssembly_torsion {K : Type*} [Field K] [CharZero K] [Module K V] {n : ℕ} (u : Fin n → V)
    (e : ℤ) (he : e ≠ 0) :
    AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i) ≤
      (AddSubgroup.closure (Set.range u)).comap (zsmulAddGroupHom e) := by sorry
