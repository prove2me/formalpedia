-- Prove2me | Theorems.Thm_Formalism_DivisionValues_R0_gramMat_conjTranspose
-- name    : Formalism.DivisionValues.R0.gramMat_conjTranspose
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:29.952321+00:00
-- url     : https://prove2.me/theorems/856c4bce-1ac9-4bb1-b036-40e05e39ea10
-- title:
--   R0: gram Mat conj Transpose
-- statement:
--   The R0 construction uses the gram Mat conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ConjTransposeEqOfPosDef.lean#L44-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ConjTransposeEqOfPosDef.lean#L44-L56

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjTransposeEqOfPosDef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.R0
variable {K : Type} [Field K] [StarRing K]

theorem Formalism.DivisionValues.R0.gramMat_conjTranspose {D m : ℕ} (Γ : Matrix (Fin D) (Fin D) K) (hΓ : Γᴴ = Γ)
    (e : Fin m → Fin D → K) :
    (Matrix.of fun a b => star (e a) ⬝ᵥ Γ.mulVec (e b))ᴴ =
      Matrix.of fun a b => star (e a) ⬝ᵥ Γ.mulVec (e b) := by sorry
