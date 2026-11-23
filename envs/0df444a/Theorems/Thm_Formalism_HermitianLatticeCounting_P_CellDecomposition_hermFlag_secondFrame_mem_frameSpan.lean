-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_CellDecomposition_hermFlag_secondFrame_mem_frameSpan
-- name    : Formalism.HermitianLatticeCounting.P.CellDecomposition.hermFlag_secondFrame_mem_frameSpan
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:12.015071+00:00
-- url     : https://prove2.me/theorems/ae2831c6-80ab-4c8e-a884-8b4ae797fb42
-- title:
--   Cell Decomposition: herm Flag second Frame mem frame Span
-- statement:
--   The Cell Decomposition construction uses the herm Flag second Frame mem frame Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LiftingDecomposition.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LiftingDecomposition.lean#L34-L37

import Definitions.Def_Formalism_FlagUnipotentLattices_LiftUnitaryFixesBase
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LiftingDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open CellDecomposition
open Formalism.HermitianLatticeCounting.P.CellDecomposition
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

theorem Formalism.HermitianLatticeCounting.P.CellDecomposition.hermFlag_secondFrame_mem_frameSpan (F F' : FlagD H r) (a : Fin (r + 1)) : F'.e a ∈ V0 F F' := by sorry
