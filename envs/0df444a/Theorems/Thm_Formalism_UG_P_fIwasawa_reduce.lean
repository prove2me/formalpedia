-- Prove2me | Theorems.Thm_Formalism_UG_P_fIwasawa_reduce
-- name    : Formalism.UG.P.fIwasawa_reduce
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:32:28.912577+00:00
-- url     : https://prove2.me/theorems/a701a68a-bed5-4c94-bbd4-8bacf3f9069f
-- title:
--   P: f Iwasawa reduce
-- statement:
--   The P construction uses the f Iwasawa reduce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawaE.lean#L184-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawaE.lean#L184-L210

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaD
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}

theorem Formalism.UG.P.fIwasawa_reduce (hσ : ∀ x, σ (σ x) = x) (hσv : ∀ x, Valued.v (σ x) = Valued.v x)
    (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) :
    ∀ r : ℕ, 2 * r ≤ n → ∃ k, fIwasawaKm σ k ∧ fIwasawaTri r (k * M) := by sorry
