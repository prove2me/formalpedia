-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_mem_idealLattice_iff
-- name    : Formalism.HermitianLattices.Ext.L3.BoxSum.mem_idealLattice_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:47:42.378793+00:00
-- url     : https://prove2.me/theorems/06e09596-d1cd-4c2b-bf69-2af10561284e
-- title:
--   Box Sum: mem ideal Lattice iff
-- statement:
--   The Box Sum construction uses the mem ideal Lattice iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemIdealLatticeIff.lean#L66-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemIdealLatticeIff.lean#L66-L75

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoTsumDivPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormEqProdOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemIdealLatticeIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology MeasureTheory Pointwise
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem Formalism.HermitianLattices.Ext.L3.BoxSum.mem_idealLattice_iff {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) (y : mixedEmbedding.mixedSpace F) :
    y ∈ mixedEmbedding.idealLattice F (fracU hI) ↔ ∃ n ∈ I, mixedEmbedding F (n : F) = y := by sorry
