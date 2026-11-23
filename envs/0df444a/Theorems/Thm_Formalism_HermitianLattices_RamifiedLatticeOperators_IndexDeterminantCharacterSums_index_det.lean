-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_RamifiedLatticeOperators_IndexDeterminantCharacterSums_index_det
-- name    : Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums.index_det
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:13.448621+00:00
-- url     : https://prove2.me/theorems/14f26d05-5dab-419c-af56-9c360a3127d5
-- title:
--   Index Determinant Character Sums: index det
-- statement:
--   The Index Determinant Character Sums construction uses the index det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/InvariantKernelTraceVanishes.lean#L35-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/InvariantKernelTraceVanishes.lean#L35-L98

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_AffineFibreCountComparison
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_InvariantKernelTraceVanishes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.RamifiedLatticeOperators Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
open Module Finset Matrix
variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums.index_det (ϖ : R) (hϖ : Irreducible ϖ) {n : Type} [Fintype n] [DecidableEq n]
    (u : Matrix n n R) (hu : u.det ≠ 0) :
    Module.length R ((n → R) ⧸ LinearMap.range u.mulVecLin) = emultiplicity ϖ u.det := by sorry
