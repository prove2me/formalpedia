-- Prove2me | Theorems.Thm_Formalism_UG_P_fSatake_borel_diag_mul
-- name    : Formalism.UG.P.fSatake_borel_diag_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:25:02.608322+00:00
-- url     : https://prove2.me/theorems/a0941656-5ff3-4378-a537-ae1a02564ac1
-- title:
--   P: f Satake borel diag mul
-- statement:
--   The P construction uses the f Satake borel diag mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FSatakeB.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FSatakeB.lean#L35-L40

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

theorem Formalism.UG.P.fSatake_borel_diag_mul {b b' : GU σ n} (hb : IsBorelU b) (hb' : IsBorelU b') (i : Fin n) :
    (((b * b' : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i =
      (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i *
      (((b' : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i := by sorry
