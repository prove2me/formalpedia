-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_upper_last
-- name    : Formalism.HermitianLatticeCounting.P.s1c2_upper_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:42:13.039821+00:00
-- url     : https://prove2.me/theorems/74e9eba6-d4eb-410a-b28b-8bb207714dad
-- title:
--   P: s1c2 upper last
-- statement:
--   The P construction uses the s1c2 upper last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L246-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L246-L250

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate TensorProduct
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.QuantumDeterminants

theorem Formalism.HermitianLatticeCounting.P.s1c2_upper_last {r : ℕ} (a : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (ha : IsUpperUnitriangular a) (b : Fin (r + 1)) :
    a (Fin.last r) b = if b = Fin.last r then 1 else 0 := by sorry
