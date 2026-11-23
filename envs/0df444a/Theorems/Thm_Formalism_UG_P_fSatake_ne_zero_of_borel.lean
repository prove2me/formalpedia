-- Prove2me | Theorems.Thm_Formalism_UG_P_fSatake_ne_zero_of_borel
-- name    : Formalism.UG.P.fSatake_ne_zero_of_borel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:24:56.570816+00:00
-- url     : https://prove2.me/theorems/7376f1ab-195b-4040-80ff-f9d37ac59dac
-- title:
--   P: f Satake ne zero of borel
-- statement:
--   The P construction uses the f Satake ne zero of borel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FSatakeC.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FSatakeC.lean#L22-L27

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
local notation "⟪" b "⟫" => (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)

theorem Formalism.UG.P.fSatake_ne_zero_of_borel {b : GU σ n} (hb : IsBorelU b) (i : Fin n) : ⟪b⟫ i i ≠ 0 := by sorry
