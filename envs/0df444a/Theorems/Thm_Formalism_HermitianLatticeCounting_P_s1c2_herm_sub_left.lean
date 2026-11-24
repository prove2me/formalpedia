-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_herm_sub_left
-- name    : Formalism.HermitianLatticeCounting.P.s1c2_herm_sub_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:42:06.292127+00:00
-- url     : https://prove2.me/theorems/0e7267c6-5776-4b19-9da7-800a779d3931
-- title:
--   P: s1c2 herm sub left
-- statement:
--   The P construction uses the s1c2 herm sub left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L193-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L193-L195

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

theorem Formalism.HermitianLatticeCounting.P.s1c2_herm_sub_left {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (u v w : ι → ℂ) :
    herm H (u - v) w = herm H u w - herm H v w := by sorry
