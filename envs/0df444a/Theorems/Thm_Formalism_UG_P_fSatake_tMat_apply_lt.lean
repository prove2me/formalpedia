-- Prove2me | Theorems.Thm_Formalism_UG_P_fSatake_tMat_apply_lt
-- name    : Formalism.UG.P.fSatake_tMat_apply_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:25:27.803764+00:00
-- url     : https://prove2.me/theorems/ab7a1581-cf9c-4403-8c7f-19f60fec5e20
-- title:
--   P: f Satake t Mat apply lt
-- statement:
--   The P construction uses the f Satake t Mat apply lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FSatakeC.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FSatakeC.lean#L29-L31

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

theorem Formalism.UG.P.fSatake_tMat_apply_lt (ϖ : L) {m : ℕ} (a : Fin m → ℤ) (j : Fin m) (hj : (j : ℕ) < n) :
    tMat ϖ n m a ⟨j, hj⟩ ⟨j, hj⟩ = ϖ ^ (a j) := by sorry
