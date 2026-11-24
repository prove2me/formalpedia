-- Prove2me | Theorems.Thm_Formalism_UG_P_mem_blockDiag_iff
-- name    : Formalism.UG.P.mem_blockDiag_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:33:24.000561+00:00
-- url     : https://prove2.me/theorems/fa5dc565-b4de-4d45-a3b4-ee3a586a725b
-- title:
--   P: mem block Diag iff
-- statement:
--   The P construction uses the mem block Diag iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Upqcpt.lean#L111-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Upqcpt.lean#L111-L132

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Upqcpt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.mem_blockDiag_iff (p q : ℕ) (g : GL (Fin p ⊕ Fin q) ℂ) :
    g ∈ Formalism.UG.blockDiag p q ↔
      Formalism.UG.Jpq p q * (g : Matrix _ _ ℂ) = (g : Matrix _ _ ℂ) * Formalism.UG.Jpq p q := by sorry
