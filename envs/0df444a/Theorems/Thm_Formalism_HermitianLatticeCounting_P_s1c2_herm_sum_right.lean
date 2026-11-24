-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_herm_sum_right
-- name    : Formalism.HermitianLatticeCounting.P.s1c2_herm_sum_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:42:16.982886+00:00
-- url     : https://prove2.me/theorems/c6f50faf-4529-4b86-93dc-d8aef0032a35
-- title:
--   P: s1c2 herm sum right
-- statement:
--   The P construction uses the s1c2 herm sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L189-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L189-L191

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

theorem Formalism.HermitianLatticeCounting.P.s1c2_herm_sum_right {ι σ : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (s : Finset σ) (c : σ → ℂ) (a : σ → ι → ℂ)
    (x : ι → ℂ) : herm H x (∑ i ∈ s, c i • a i) = ∑ i ∈ s, star (c i) * herm H x (a i) := by sorry
