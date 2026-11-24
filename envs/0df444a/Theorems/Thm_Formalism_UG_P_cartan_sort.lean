-- Prove2me | Theorems.Thm_Formalism_UG_P_cartan_sort
-- name    : Formalism.UG.P.cartan_sort
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:30:45.945734+00:00
-- url     : https://prove2.me/theorems/9ac80cdf-611e-4490-8240-26753b8f28ba
-- title:
--   P: cartan sort
-- statement:
--   The P construction uses the cartan sort property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Cartan.lean#L239-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Cartan.lean#L239-L252

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

theorem Formalism.UG.P.cartan_sort (ϖ : L) {m : ℕ} (a : Fin m → ℤ) :
    ∃ a' : Fin m → ℤ, Antitone a' ∧ ∃ S₁ ∈ GLint (Fin m) O, ∃ S₂ ∈ GLint (Fin m) O,
      Matrix.diagonal (fun i => ϖ ^ a i) = (S₁ : Matrix (Fin m) (Fin m) L) *
        Matrix.diagonal (fun i => ϖ ^ a' i) * (S₂ : Matrix (Fin m) (Fin m) L) := by sorry
