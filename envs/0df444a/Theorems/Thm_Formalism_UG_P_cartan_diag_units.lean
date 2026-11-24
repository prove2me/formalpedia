-- Prove2me | Theorems.Thm_Formalism_UG_P_cartan_diag_units
-- name    : Formalism.UG.P.cartan_diag_units
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:31:24.275065+00:00
-- url     : https://prove2.me/theorems/fe63fb1a-fb73-4523-8e24-a9463ef89209
-- title:
--   P: cartan diag units
-- statement:
--   The P construction uses the cartan diag units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Cartan.lean#L254-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Cartan.lean#L254-L289

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] (O : Subring L) {Γ : Type} [LinearOrderedCommGroupWithZero Γ]

theorem Formalism.UG.P.cartan_diag_units (val : Valuation L Γ) (hO : ∀ x, x ∈ O ↔ val x ≤ 1) (ϖ : L)
    (hϖ0 : ϖ ≠ 0) (hU : ∀ x : L, x ≠ 0 → ∃ k : ℤ, val x = val ϖ ^ k) {m : ℕ} (d : Fin m → L)
    (hd : ∀ i, d i ≠ 0) :
    ∃ a : Fin m → ℤ, ∃ U ∈ GLint (Fin m) O,
      Matrix.diagonal d = (U : Matrix (Fin m) (Fin m) L) * Matrix.diagonal (fun i => ϖ ^ a i) := by sorry
