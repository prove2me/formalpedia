-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_majLattice_mem_span
-- name    : Formalism.HermitianLatticesTheory.majLattice_mem_span
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:01.287388+00:00
-- url     : https://prove2.me/theorems/fd84b29c-2888-4911-a864-e28ef327164b
-- title:
--   Hermitian Lattices Theory: maj Lattice mem span
-- statement:
--   The Hermitian Lattices Theory construction uses the maj Lattice mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/MajLattice.lean#L93-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/MajLattice.lean#L93-L109

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CommonMajorizingLattice
import Definitions.Def_Lemmata_GeneralBFactSecondRest_Imports
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module
open scoped Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V ι : Type*} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K] [AddCommGroup V]
  [Module K V] [Fintype ι] [DecidableEq ι]

theorem Formalism.HermitianLatticesTheory.majLattice_mem_span (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (x : V) (hx : ∀ i, IsIntegral ℤ (b.repr x i)) :
    realize b X x ∈ Submodule.span ℤ (Set.range (majLattice_B X hX)) := by sorry
