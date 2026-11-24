-- Prove2me | Theorems.Thm_Formalism_UG_P_polyAct_weyl_gen
-- name    : Formalism.UG.P.polyAct_weyl_gen
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:33:17.136967+00:00
-- url     : https://prove2.me/theorems/4169258c-d04f-47be-aab9-0d16c4370194
-- title:
--   P: poly Act weyl gen
-- statement:
--   The P construction uses the poly Act weyl gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/LinSubstIsHomogeneous.lean#L82-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/LinSubstIsHomogeneous.lean#L82-L107

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LinSubstIsHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open Formalism Formalism.UG Formalism.UG.P
variable {O : Type} [CommRing O] {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.polyAct_weyl_gen (g : GL n O) (K : ℕ) (α : n →₀ ℕ) (hα : α.degree = K) :
    polyAct O n g (monomial α (α.multinomial : O)) ∈ weylSub O n K := by sorry
