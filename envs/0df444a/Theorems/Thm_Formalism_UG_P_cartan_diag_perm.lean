-- Prove2me | Theorems.Thm_Formalism_UG_P_cartan_diag_perm
-- name    : Formalism.UG.P.cartan_diag_perm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:30:48.701005+00:00
-- url     : https://prove2.me/theorems/c6eb2bf2-8128-4766-9081-ac63863a2c12
-- title:
--   P: cartan diag perm
-- statement:
--   The P construction uses the cartan diag perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Cartan.lean#L230-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Cartan.lean#L230-L237

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

theorem Formalism.UG.P.cartan_diag_perm {m : ℕ} (d : Fin m → L) (σ : Equiv.Perm (Fin m)) :
    Matrix.diagonal d = σ.symm.toPEquiv.toMatrix * Matrix.diagonal (d ∘ σ) * σ.toPEquiv.toMatrix := by sorry
