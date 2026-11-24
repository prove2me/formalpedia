-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_UW_sub_S
-- name    : Formalism.HermitianLatticeCounting.P.s1c2_UW_sub_S
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:42:08.45771+00:00
-- url     : https://prove2.me/theorems/2f0a879a-1078-4eee-9a43-45aca958d4d1
-- title:
--   P: s1c2 UW sub S
-- statement:
--   The P construction uses the s1c2 UW sub S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L429-L431
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L429-L431

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

theorem Formalism.HermitianLatticeCounting.P.s1c2_UW_sub_S (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hh : h ∈ UWset k r z) : h ∈ Sset k r z := by sorry
