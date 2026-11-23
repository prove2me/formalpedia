-- Prove2me | Theorems.Thm_Formalism_UG_P_fSatake_cTJ
-- name    : Formalism.UG.P.fSatake_cTJ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:53.582812+00:00
-- url     : https://prove2.me/theorems/100576c7-56aa-4a54-8d84-09f73ed22662
-- title:
--   P: f Satake c TJ
-- statement:
--   The P construction uses the f Satake c TJ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FSatakeB.lean#L54-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FSatakeB.lean#L54-L62

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
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

theorem Formalism.UG.P.fSatake_cTJ (M : Matrix (Fin n) (Fin n) L) (i l : Fin n) :
    (cT σ M * antiJ L n) i l = σ (M l.rev i) := by sorry
