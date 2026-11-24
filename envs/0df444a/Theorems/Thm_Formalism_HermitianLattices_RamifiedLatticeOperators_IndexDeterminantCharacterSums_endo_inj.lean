-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_RamifiedLatticeOperators_IndexDeterminantCharacterSums_endo_inj
-- name    : Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums.endo_inj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:59:51.502801+00:00
-- url     : https://prove2.me/theorems/9be95d92-fdf8-4f94-bd07-5c9221940d88
-- title:
--   Index Determinant Character Sums: endo inj
-- statement:
--   The Index Determinant Character Sums construction uses the endo inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/InvariantKernelTraceVanishes.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/InvariantKernelTraceVanishes.lean#L30-L33

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

theorem Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums.endo_inj {n : Type} [Fintype n] [DecidableEq n] (P : (n → R) →ₗ[R] (n → R))
    (hP : LinearMap.det P ≠ 0) : Function.Injective P := by sorry
