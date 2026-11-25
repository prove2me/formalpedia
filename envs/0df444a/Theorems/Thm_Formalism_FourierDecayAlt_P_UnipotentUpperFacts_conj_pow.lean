-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentUpperFacts_conj_pow
-- name    : Formalism.FourierDecayAlt.P.UnipotentUpperFacts.conj_pow
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:28:41.945445+00:00
-- url     : https://prove2.me/theorems/e2151f5e-9eef-41a4-8801-8a065bb20b9d
-- title:
--   Unipotent Upper Facts: conj pow
-- statement:
--   The Unipotent Upper Facts construction uses the conj pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentUpperFacts.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentUpperFacts.lean#L31-L37

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedPointsGramVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentUpperFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.UnipotentUpperFacts
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

theorem Formalism.FourierDecayAlt.P.UnipotentUpperFacts.conj_pow (γ X : Matrix n n ℂ) (hγ : IsUnit γ.det) (p : ℕ) : (γ⁻¹ * X * γ) ^ p = γ⁻¹ * X ^ p * γ := by sorry
