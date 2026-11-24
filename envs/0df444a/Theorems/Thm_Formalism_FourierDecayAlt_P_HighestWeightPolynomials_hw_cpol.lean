-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HighestWeightPolynomials_hw_cpol
-- name    : Formalism.FourierDecayAlt.P.HighestWeightPolynomials.hw_cpol
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:29:12.882554+00:00
-- url     : https://prove2.me/theorems/872463e5-bd91-447b-91cf-80787427c947
-- title:
--   Highest Weight Polynomials: hw cpol
-- statement:
--   The Highest Weight Polynomials construction uses the hw cpol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HighestWeightPolynomials.lean#L88-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HighestWeightPolynomials.lean#L88-L97

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

theorem Formalism.FourierDecayAlt.P.HighestWeightPolynomials.hw_cpol {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {m ν : Fin n → ℂ} {v : V} (hE : GlRel E)
    (hv : v ∈ CapSp E m) (hv0 : v ≠ 0) (hw : IsHW E ν v) (w : ℂ) :
    cpol m w = cpol (fun k => ν k - ((k : ℕ) : ℂ)) w := by sorry
