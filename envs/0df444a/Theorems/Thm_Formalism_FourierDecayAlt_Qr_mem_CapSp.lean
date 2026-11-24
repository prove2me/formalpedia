-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Qr_mem_CapSp
-- name    : Formalism.FourierDecayAlt.Qr.mem_CapSp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:30:07.363844+00:00
-- url     : https://prove2.me/theorems/c2a2e2fa-f54b-4057-9e25-4e68eadae161
-- title:
--   Qr: mem Cap Sp
-- statement:
--   The Qr construction uses the mem Cap Sp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/CapelliDeterminantAndBranching.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/CapelliDeterminantAndBranching.lean#L26-L29

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem Formalism.FourierDecayAlt.Qr.mem_CapSp {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {m : Fin n → ℂ} {v : V} :
    v ∈ CapSp E m ↔ ∀ w, qdet E w v = cpol m w • v := by sorry
