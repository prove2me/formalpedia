-- Prove2me | Theorems.Thm_Formalism_UG_P_fSatake_unit_diag_mat
-- name    : Formalism.UG.P.fSatake_unit_diag_mat
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:31:43.760325+00:00
-- url     : https://prove2.me/theorems/f4706703-c96e-4cc8-b471-201430c12f76
-- title:
--   P: f Satake unit diag mat
-- statement:
--   The P construction uses the f Satake unit diag mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FSatakeB.lean#L64-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FSatakeB.lean#L64-L80

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

theorem Formalism.UG.P.fSatake_unit_diag_mat {M : Matrix (Fin n) (Fin n) L} (hb : ∀ i j : Fin n, j < i → M i j = 0)
    (hU : cT σ M * antiJ L n * M = antiJ L n) (i : Fin n) : σ (M i i) * M i.rev i.rev = 1 := by sorry
