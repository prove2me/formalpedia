-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_S_cols
-- name    : Formalism.HermitianLatticeCounting.P.s1c2_S_cols
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:42:03.532807+00:00
-- url     : https://prove2.me/theorems/7cc3ff8d-084d-4f9b-8166-0371248e7e81
-- title:
--   P: s1c2 S cols
-- statement:
--   The P construction uses the s1c2 S cols property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L309-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L309-L313

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

theorem Formalism.HermitianLatticeCounting.P.s1c2_S_cols (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hs : s ∈ Sset k r z) :
    ∃ U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, IsUpperUnitriangular U ∧ ∀ b, s *ᵥ fvec k r z b = ∑ e, U e b • fvec k r z e := by sorry
