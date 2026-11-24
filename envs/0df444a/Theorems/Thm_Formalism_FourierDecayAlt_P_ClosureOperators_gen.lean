-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_gen
-- name    : Formalism.FourierDecayAlt.P.ClosureOperators.gen
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:48:39.418801+00:00
-- url     : https://prove2.me/theorems/3358e575-2749-470c-b69a-b4b59d2487f0
-- title:
--   Closure Operators: gen
-- statement:
--   The Closure Operators construction uses the gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ClosureOperators.lean#L31-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ClosureOperators.lean#L31-L69

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

theorem Formalism.FourierDecayAlt.P.ClosureOperators.gen {N : ℕ} {E : Fin N → Fin N → Module.End ℂ V} (hE : GlRel E) (T L : Fin N → Fin N → Prop)
    (M : Submodule ℂ V)
    (h0 : ∀ a b, T a b → ∀ m ∈ M, E a b m ∈ Cl E L M)
    (h1 : ∀ a b c d, T a b → L c d → b = c → T a d ∨ L a d)
    (h2 : ∀ a b c d, T a b → L c d → d = a → T c b ∨ L c b) :
    ∀ a b, T a b → ∀ q ∈ Cl E L M, E a b q ∈ Cl E L M := by sorry
