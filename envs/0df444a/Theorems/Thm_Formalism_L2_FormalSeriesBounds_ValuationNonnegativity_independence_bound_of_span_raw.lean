-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_independence_bound_of_span_raw
-- name    : Formalism.L2.FormalSeriesBounds.ValuationNonnegativity.independence_bound_of_span_raw
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:19:18.800109+00:00
-- url     : https://prove2.me/theorems/a76af8ff-e107-4031-b724-2211de2a2bcd
-- title:
--   Valuation Nonnegativity: independence bound of span raw
-- statement:
--   The Valuation Nonnegativity construction uses the independence bound of span raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/IndependenceBoundRaw.lean#L165-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/IndependenceBoundRaw.lean#L165-L210

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IndependenceBoundRaw
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
variable {C : Type} [Field C] {V : VF C}
variable {d : ℕ} {I J : Type} [Fintype I] [Fintype J]

theorem Formalism.L2.FormalSeriesBounds.ValuationNonnegativity.independence_bound_of_span_raw [IsAlgClosed C] (X : Cart V d I J) (a : ZMod d) (m : ℕ)
    (hR2 : ∀ (w : I → C) (x : ℕ → I ⊕ J → C), X.Good a w x → (∀ q, V.MM (X.c0' x q)) → ∀ c, V.MM (w c))
    (e : Fin m → J → C)
    (hspan : ∀ (w : I → C) (x : ℕ → I ⊕ J → C), X.Good a w x → (∀ c, V.MM (X.V2 x c)) →
      ∃ b : Fin m → C, ∀ q, V.MM (X.c0' x q ^ V.l - ∑ r, b r * e r q))
    (N : ℕ) (w : Fin N → I → C) (x : Fin N → ℕ → I ⊕ J → C) (hg : ∀ ν, X.Good a (w ν) (x ν))
    (hV : ∀ ν c, V.MM (X.V2 (x ν) c)) (hind : IndepMod V w) : N ≤ m := by sorry
