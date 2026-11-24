-- Prove2me | Theorems.Thm_Formalism_UG_P_fSatake_unit_diag
-- name    : Formalism.UG.P.fSatake_unit_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:35.483083+00:00
-- url     : https://prove2.me/theorems/dbec26b9-61aa-4dba-9b6e-5059106aa0d5
-- title:
--   P: f Satake unit diag
-- statement:
--   The P construction uses the f Satake unit diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FSatakeB.lean#L82-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FSatakeB.lean#L82-L85

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

theorem Formalism.UG.P.fSatake_unit_diag {b : GU σ n} (hb : IsBorelU b) (i : Fin n) :
    σ ((((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) *
      (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i.rev i.rev = 1 := by sorry
