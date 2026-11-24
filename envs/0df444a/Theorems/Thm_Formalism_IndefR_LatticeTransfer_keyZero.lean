-- Prove2me | Theorems.Thm_Formalism_IndefR_LatticeTransfer_keyZero
-- name    : Formalism.IndefR.LatticeTransfer.keyZero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:14.695997+00:00
-- url     : https://prove2.me/theorems/09aa53dc-ad55-4bed-bc82-b154ad86ceb7
-- title:
--   Lattice Transfer: key Zero
-- statement:
--   The Lattice Transfer construction uses the key Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinrankIntSelf.lean#L197-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinrankIntSelf.lean#L197-L200

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinrankIntSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
open IdempotentLemmas

theorem Formalism.IndefR.LatticeTransfer.keyZero : KeyZero := by sorry
