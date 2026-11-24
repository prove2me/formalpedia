-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_adj_last
-- name    : Formalism.HermitianLatticeCounting.P.s1c2_adj_last
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:42:45.789816+00:00
-- url     : https://prove2.me/theorems/7438cd74-e439-4631-8e71-2fd4bcf087f5
-- title:
--   P: s1c2 adj last
-- statement:
--   The P construction uses the s1c2 adj last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L252-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L252-L263

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

theorem Formalism.HermitianLatticeCounting.P.s1c2_adj_last {r : ℕ} (B : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hB : IsUpperUnitriangular B) (c : Fin (r + 1)) :
    B.adjugate (Fin.last r) c = if c = Fin.last r then 1 else 0 := by sorry
