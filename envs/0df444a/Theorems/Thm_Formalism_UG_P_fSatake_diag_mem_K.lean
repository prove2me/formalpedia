-- Prove2me | Theorems.Thm_Formalism_UG_P_fSatake_diag_mem_K
-- name    : Formalism.UG.P.fSatake_diag_mem_K
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:32:11.528155+00:00
-- url     : https://prove2.me/theorems/e7c79cf5-4227-4689-9643-96a26d6e9353
-- title:
--   P: f Satake diag mem K
-- statement:
--   The P construction uses the f Satake diag mem K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FSatakeC.lean#L101-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FSatakeC.lean#L101-L135

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

theorem Formalism.UG.P.fSatake_diag_mem_K {d : GU σ n} {e : Fin n → L} (hd : ⟪d⟫ = Matrix.diagonal e)
    (hd' : ⟪d⁻¹⟫ = Matrix.diagonal (fun i => (e i)⁻¹)) (hv : ∀ i, Valued.v (e i) = 1) :
    d ∈ KU σ n := by sorry
