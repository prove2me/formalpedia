-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_herm_sum_left
-- name    : Formalism.HermitianLatticeCounting.P.s1c2_herm_sum_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:01.914478+00:00
-- url     : https://prove2.me/theorems/03b3e406-f8fd-411d-a4c9-92ca2e02770c
-- title:
--   P: s1c2 herm sum left
-- statement:
--   The P construction uses the s1c2 herm sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L185-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L185-L187

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

theorem Formalism.HermitianLatticeCounting.P.s1c2_herm_sum_left {ι σ : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (s : Finset σ) (c : σ → ℂ) (a : σ → ι → ℂ)
    (y : ι → ℂ) : herm H (∑ i ∈ s, c i • a i) y = ∑ i ∈ s, c i * herm H (a i) y := by sorry
