-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationFitting_pow_frob
-- name    : Formalism.L2.FormalSeriesBounds.ValuationFitting.pow_frob
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T18:34:14.080397+00:00
-- url     : https://prove2.me/theorems/e9e88722-12de-4ff5-bc35-559f77715df9
-- title:
--   Valuation Fitting: pow frob
-- statement:
--   The Valuation Fitting construction uses the pow frob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PlugUP.lean#L87-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PlugUP.lean#L87-L94

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_DualLattices_U10
import Definitions.Def_ReciprocityTheory_DualLattices_KilledGen
import Definitions.Def_ReciprocityTheory_DualLattices_IdemGen
import Definitions.Def_ReciprocityTheory_DualLattices_LenEx
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_FittingIdeal_DetMulMemFitt0
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PlugUP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
open Formalism.L2.FormalSeriesBounds.ValuationFitting
open ReciprocityTheory.PGsh.Up CharacteristicFromRanks
variable {C : Type} [Field C]

theorem Formalism.L2.FormalSeriesBounds.ValuationFitting.pow_frob {m : ℕ} {d : ℕ} (φ : Equiv.Perm (Fin m)) (ix : ZMod d → Fin m)
    (hφ : ∀ a, φ (ix a) = ix (a + 1)) (a : ZMod d) : ∀ k : ℕ, (φ ^ k) (ix a) = ix (a + (k : ZMod d))
  := by sorry
