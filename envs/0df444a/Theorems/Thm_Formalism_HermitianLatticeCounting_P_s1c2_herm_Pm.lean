-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_herm_Pm
-- name    : Formalism.HermitianLatticeCounting.P.s1c2_herm_Pm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:45.830875+00:00
-- url     : https://prove2.me/theorems/e7342674-537d-4b78-b21d-a0b37a2de9f2
-- title:
--   P: s1c2 herm Pm
-- statement:
--   The P construction uses the s1c2 herm Pm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L354-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L354-L359

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

theorem Formalism.HermitianLatticeCounting.P.s1c2_herm_Pm (k r : ℕ) (z' x : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') :
    herm (Hpk k r) (reflectFlagCoordinates k r x) z' = herm (Hpk k r) x z' := by sorry
