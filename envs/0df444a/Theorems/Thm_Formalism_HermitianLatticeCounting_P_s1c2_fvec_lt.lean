-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_fvec_lt
-- name    : Formalism.HermitianLatticeCounting.P.s1c2_fvec_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:16:38.707967+00:00
-- url     : https://prove2.me/theorems/88fe206e-7af8-4d83-9166-2f0a46fade94
-- title:
--   P: s1c2 fvec lt
-- statement:
--   The P construction uses the s1c2 fvec lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L367-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L367-L369

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

theorem Formalism.HermitianLatticeCounting.P.s1c2_fvec_lt (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (b : Fin (r + 1)) (hb : b.val < r) :
    fvec k r z b = bvec (eI k r ⟨b.val, hb⟩) := by sorry
