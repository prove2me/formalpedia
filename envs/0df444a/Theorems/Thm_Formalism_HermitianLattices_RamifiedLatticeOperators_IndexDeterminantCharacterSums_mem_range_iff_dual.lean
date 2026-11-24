-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_RamifiedLatticeOperators_IndexDeterminantCharacterSums_mem_range_iff_dual
-- name    : Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums.mem_range_iff_dual
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:59:48.59609+00:00
-- url     : https://prove2.me/theorems/e5e685b3-f426-4744-9645-aa179aa7dc81
-- title:
--   Index Determinant Character Sums: mem range iff dual
-- statement:
--   The Index Determinant Character Sums construction uses the mem range iff dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/InvariantKernelTraceVanishes.lean#L402-L429
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/InvariantKernelTraceVanishes.lean#L402-L429

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
variable {F : Type} [Field F] [Fintype F]

theorem Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums.mem_range_iff_dual {m k : Type} [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]
    (A : Matrix m k F) (v : m → F) :
    v ∈ LinearMap.range A.mulVecLin ↔ ∀ w : m → F, Aᵀ *ᵥ w = 0 → w ⬝ᵥ v = 0 := by sorry
