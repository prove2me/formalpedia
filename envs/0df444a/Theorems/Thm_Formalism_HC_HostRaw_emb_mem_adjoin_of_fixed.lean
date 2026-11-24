-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_emb_mem_adjoin_of_fixed
-- name    : Formalism.HC.HostRaw.emb_mem_adjoin_of_fixed
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:58:46.810598+00:00
-- url     : https://prove2.me/theorems/5d1a10f8-58dd-459d-be8e-838e9ef7492b
-- title:
--   Host Raw: emb mem adjoin of fixed
-- statement:
--   The Host Raw construction uses the emb mem adjoin of fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/CycImage.lean#L14-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/CycImage.lean#L14-L31

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_CycImage
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.HC Formalism.HC.HostRaw
open Formalism.FrobeniusOrbits Formalism.HC.Der
variable {φ : Frame} (H : HostRaw φ)

theorem Formalism.HC.HostRaw.emb_mem_adjoin_of_fixed {m : ℕ} (hm : m ∣ H.condN) (x : H.E)
    (hx : ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD m] → H.gal.symm (H.art u) x = x) :
    emb H x ∈ adjoin ℚ {y : Cond.Cyc H.condN | y ^ m = 1} := by sorry
