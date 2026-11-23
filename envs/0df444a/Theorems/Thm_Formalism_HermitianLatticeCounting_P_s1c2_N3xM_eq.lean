-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_N3xM_eq
-- name    : Formalism.HermitianLatticeCounting.P.s1c2_N3xM_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:19.345803+00:00
-- url     : https://prove2.me/theorems/b9eb46ff-c2d3-41a8-967a-2c0b3d0d54bf
-- title:
--   P: s1c2 N3x M eq
-- statement:
--   The P construction uses the s1c2 N3x M eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L305-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L305-L307

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

theorem Formalism.HermitianLatticeCounting.P.s1c2_N3xM_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    formalDeterminantVectorOnGroup k r z z' g = formalDeterminantVector (hermitianSesquilinearForm (Hpk k r)) (fun a => g⁻¹ *ᵥ fvec k r z a) (fvec k r z') := by sorry
