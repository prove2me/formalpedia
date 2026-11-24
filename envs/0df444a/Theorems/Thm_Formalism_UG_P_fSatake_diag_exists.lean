-- Prove2me | Theorems.Thm_Formalism_UG_P_fSatake_diag_exists
-- name    : Formalism.UG.P.fSatake_diag_exists
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:32:10.052906+00:00
-- url     : https://prove2.me/theorems/34dc2310-d988-4847-b50d-a5e0552bf656
-- title:
--   P: f Satake diag exists
-- statement:
--   The P construction uses the f Satake diag exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FSatakeB.lean#L87-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FSatakeB.lean#L87-L114

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

theorem Formalism.UG.P.fSatake_diag_exists (e : Fin n → L) (he : ∀ i, σ (e i) * e i.rev = 1) :
    ∃ d : GU σ n, (((d : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal e ∧
      (((d⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        Matrix.diagonal (fun i => (e i)⁻¹) := by sorry
