-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_top_of_stab
-- name    : Formalism.FourierDecayAlt.P.ClosureOperators.top_of_stab
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:48:31.445809+00:00
-- url     : https://prove2.me/theorems/3c09dd95-e965-4fb9-bdac-3d88eb685152
-- title:
--   Closure Operators: top of stab
-- statement:
--   The Closure Operators construction uses the top of stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ClosureOperators.lean#L149-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ClosureOperators.lean#L149-L153

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ClosureOperators
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ClosureOperators
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem Formalism.FourierDecayAlt.P.ClosureOperators.top_of_stab {N : ℕ} {E : Fin N → Fin N → Module.End ℂ V} (hI : Irr E) (S : Submodule ℂ V) (hS : Stab E S)
    (v : V) (hv : v ∈ S) (hv0 : v ≠ 0) : S = ⊤ := by sorry
