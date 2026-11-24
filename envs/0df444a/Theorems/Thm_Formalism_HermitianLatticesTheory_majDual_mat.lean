-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_majDual_mat
-- name    : Formalism.HermitianLatticesTheory.majDual_mat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:48.961575+00:00
-- url     : https://prove2.me/theorems/8fc51b3e-c468-46ba-bc30-7a19b7f0eec2
-- title:
--   Hermitian Lattices Theory: maj Dual mat
-- statement:
--   The Hermitian Lattices Theory construction uses the maj Dual mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/MajDual.lean#L54-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/MajDual.lean#L54-L60

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

theorem Formalism.HermitianLatticesTheory.majDual_mat (G X : Matrix ι ι ℂ) (hX : IsUnit X.det) (a c : ι → ℂ) :
    dotProduct (star (X⁻¹.mulVec a)) (((X.conjTranspose * G * X)).mulVec (X⁻¹.mulVec c)) =
      dotProduct (star a) (G.mulVec c) := by sorry
