-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BranchingSystems_fin_cap
-- name    : Formalism.FourierDecayAlt.P.BranchingSystems.fin_cap
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:51:14.589522+00:00
-- url     : https://prove2.me/theorems/16373dcc-4cba-4435-af5f-adef765e0d36
-- title:
--   Branching Systems: fin cap
-- statement:
--   The Branching Systems construction uses the fin cap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BranchingSystems.lean#L173-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BranchingSystems.lean#L173-L204

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BranchingSystems
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BranchingSystems
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem Formalism.FourierDecayAlt.P.BranchingSystems.fin_cap {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (β : ℂ) (M : Fin n → ℤ) (i : Fin n) :
    {t : ℤ | CapSp E (shf β (Function.update M i t)) ≠ ⊥}.Finite := by sorry
