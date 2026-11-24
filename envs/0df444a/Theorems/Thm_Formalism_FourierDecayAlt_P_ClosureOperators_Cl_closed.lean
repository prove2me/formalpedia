-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_Cl_closed
-- name    : Formalism.FourierDecayAlt.P.ClosureOperators.Cl_closed
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:49:07.055834+00:00
-- url     : https://prove2.me/theorems/cbd53eee-b129-4c1a-9688-2824c63a648b
-- title:
--   Closure Operators: Cl closed
-- statement:
--   The Closure Operators construction uses the Cl closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ClosureOperators.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ClosureOperators.lean#L20-L25

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

theorem Formalism.FourierDecayAlt.P.ClosureOperators.Cl_closed {N : ℕ} {E : Fin N → Fin N → Module.End ℂ V} {L : Fin N → Fin N → Prop} {M : Submodule ℂ V}
    (a b : Fin N) (h : L a b) (q : V) (hq : q ∈ Cl E L M) : E a b q ∈ Cl E L M := by sorry
