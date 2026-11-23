-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_hL_apply
-- name    : Formalism.HermitianLatticeCounting.P.s1c2_hL_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:16:53.780843+00:00
-- url     : https://prove2.me/theorems/ff746fde-63e2-4086-b29d-8ef4a416e9ee
-- title:
--   P: s1c2 h L apply
-- statement:
--   The P construction uses the s1c2 h L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L183-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L183-L183

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

theorem Formalism.HermitianLatticeCounting.P.s1c2_hL_apply {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (x y : ι → ℂ) : hermitianSesquilinearForm H x y = herm H x y := by sorry
