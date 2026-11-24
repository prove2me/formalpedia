-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HighestWeightPolynomials_indep_char
-- name    : Formalism.FourierDecayAlt.P.HighestWeightPolynomials.indep_char
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:28:50.880464+00:00
-- url     : https://prove2.me/theorems/33eaff0c-4c0b-467b-bd30-581638a7abe5
-- title:
--   Highest Weight Polynomials: indep char
-- statement:
--   The Highest Weight Polynomials construction uses the indep char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HighestWeightPolynomials.lean#L84-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HighestWeightPolynomials.lean#L84-L86

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Lemmata_GeneralBFactSecondTerForm_Imports
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HighestWeightPolynomials
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HighestWeightPolynomials
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem Formalism.FourierDecayAlt.P.HighestWeightPolynomials.indep_char {ι : Type*} (C : ℂ → Module.End ℂ V) (χ : ι → ℂ → ℂ) (hχ : Function.Injective χ)
    (p : ι → Submodule ℂ V) (hp : ∀ i v, v ∈ p i ↔ ∀ w, C w v = χ i w • v) : iSupIndep p := by sorry
