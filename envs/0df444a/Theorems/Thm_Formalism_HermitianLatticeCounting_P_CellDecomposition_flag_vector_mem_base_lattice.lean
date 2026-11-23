-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_CellDecomposition_flag_vector_mem_base_lattice
-- name    : Formalism.HermitianLatticeCounting.P.CellDecomposition.flag_vector_mem_base_lattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:14.782082+00:00
-- url     : https://prove2.me/theorems/61be82e4-8043-4c32-a8c6-482a5e27a605
-- title:
--   Cell Decomposition: flag vector mem base lattice
-- statement:
--   The Cell Decomposition construction uses the flag vector mem base lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LiftingDecomposition.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LiftingDecomposition.lean#L29-L32

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

theorem Formalism.HermitianLatticeCounting.P.CellDecomposition.flag_vector_mem_base_lattice (F F' : FlagD H r) (a : Fin (r + 1)) : F.e a ∈ V0 F F' := by sorry
