-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_om_eq
-- name    : Formalism.HermitianLatticeCounting.P.s1c2_om_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:16:41.999674+00:00
-- url     : https://prove2.me/theorems/0f0ef87f-e3de-4bb1-97d0-43825cb1cc5d
-- title:
--   P: s1c2 om eq
-- statement:
--   The P construction uses the s1c2 om eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L333-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L333-L341

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

theorem Formalism.HermitianLatticeCounting.P.s1c2_om_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z')
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    N3om k r z z' g = reflectFlagCoordinates k r (formalDeterminantVectorOnGroup k r z z' g) +
      (herm (Hpk k r) (formalDeterminantVectorOnGroup k r z z' g) z' / (Tz k r z' : ℂ)) • z' := by sorry
