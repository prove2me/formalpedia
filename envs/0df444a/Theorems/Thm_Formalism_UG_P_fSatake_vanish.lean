-- Prove2me | Theorems.Thm_Formalism_UG_P_fSatake_vanish
-- name    : Formalism.UG.P.fSatake_vanish
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:32:26.376067+00:00
-- url     : https://prove2.me/theorems/91ce31a5-4a6e-41b8-8c89-34ac69d479a3
-- title:
--   P: f Satake vanish
-- statement:
--   The P construction uses the f Satake vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FSatakeC.lean#L485-L524
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FSatakeC.lean#L485-L524

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

theorem Formalism.UG.P.fSatake_vanish (hSph : SphericalExistsU) [CompleteSpace L] {ϖ : L} {q m : ℕ}
    (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n) (hm' : n ≤ 2 * m + 1) {α : Fin m → ℂ}
    (hα : ∀ i, α i ≠ 0) {φ : GU σ n → ℂ} (hφ : IsSphericalU q α φ) (x : GU σ n)
    (hx : ¬ ∃ b k : GU σ n, IsBorelU b ∧ k ∈ KU σ n ∧ x = b * k) : φ x = 0 := by sorry
