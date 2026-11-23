-- Prove2me | Theorems.Thm_Automata_acc_omega_lang_inter2
-- name    : Automata.acc_omega_lang_inter2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:28:58.412665+00:00
-- url     : https://prove2.me/theorems/58f170cd-b2cc-4f65-9cd0-4c4691ae8df9
-- title:
--   Automata: acc omega lang inter2
-- statement:
--   The ω-language accepted by the OI2 NA is the intersection
--   of the ω-languages accepted by `M0` and `M1`.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/OI2.lean#L140-L184
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/OI2.lean#L140-L184

import Definitions.Def_AutomataTheory_Automata_Prod
import Definitions.Def_AutomataTheory_Automata_Hist
import Definitions.Def_AutomataTheory_Sequences_Temporal
import Definitions.Def_AutomataTheory_Automata_OI2
set_option autoImplicit true
open Function Set Filter Stream'
open Automata
open Classical
variable {A : Type} (M : Fin 2 → NA A) (acc : (i : Fin 2) → Set ((M i).State))

theorem Automata.acc_omega_lang_inter2 :
    (NA.OI2 M acc).AcceptedOmegaLang (NA.OI2_Acc M acc) = ⋂ i : Fin 2, (M i).AcceptedOmegaLang (acc i) := by sorry
