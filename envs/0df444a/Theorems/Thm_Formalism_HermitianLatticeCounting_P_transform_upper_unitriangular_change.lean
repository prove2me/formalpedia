-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_transform_upper_unitriangular_change
-- name    : Formalism.HermitianLatticeCounting.P.transform_upper_unitriangular_change
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:01.256317+00:00
-- url     : https://prove2.me/theorems/dd321af2-3ff6-437d-be45-13569795cb69
-- title:
--   P: transform upper unitriangular change
-- statement:
--   The P construction uses the transform upper unitriangular change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L265-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorAbsoluteOfExplicit.lean#L265-L303

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

theorem Formalism.HermitianLatticeCounting.P.transform_upper_unitriangular_change {ι : Type} [Fintype ι] [DecidableEq ι] (H η : Matrix ι ι ℂ) (hη : η ∈ UH H)
    (hηu : IsUnit η.det) {r : ℕ} (y f' : Fin (r + 1) → ι → ℂ) (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hA : IsUpperUnitriangular A) (hA' : IsUpperUnitriangular A') (hf : ∀ b, η *ᵥ f' b = ∑ c, A' c b • f' c) :
    formalDeterminantVector (hermitianSesquilinearForm H) (fun a => η⁻¹ *ᵥ ∑ e, A e a • y e) f' = η⁻¹ *ᵥ formalDeterminantVector (hermitianSesquilinearForm H) y f' := by sorry
