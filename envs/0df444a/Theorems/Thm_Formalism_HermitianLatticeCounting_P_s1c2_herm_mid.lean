-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_herm_mid
-- name    : Formalism.HermitianLatticeCounting.P.s1c2_herm_mid
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:42:10.05653+00:00
-- url     : https://prove2.me/theorems/7059fc01-c625-4492-a30d-22c6d5ddf136
-- title:
--   P: s1c2 herm mid
-- statement:
--   The P construction uses the s1c2 herm mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L343-L352
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L343-L352

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

theorem Formalism.HermitianLatticeCounting.P.s1c2_herm_mid (k r : ℕ) (z' d : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z')
    (hd : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → d i = 0) : herm (Hpk k r) d z' = 0 := by sorry
