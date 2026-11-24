-- Prove2me | Theorems.Thm_Formalism_HC_D7_decomp_d
-- name    : Formalism.HC.D7.decomp_d
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:39:26.487056+00:00
-- url     : https://prove2.me/theorems/0abac98a-03d3-4438-9ec1-70c3283bc82d
-- title:
--   D7: decomp d
-- statement:
--   The D7 construction uses the decomp d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ArtinMapSecondEqJacobiSymOfModEq.lean#L352-L372
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ArtinMapSecondEqJacobiSymOfModEq.lean#L352-L372

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.D7
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {q d : ℕ} (e : ℕ) (hH : HostHyp q d)
include hH

theorem Formalism.HC.D7.decomp_d (ud : (ZMod (2 ^ (e + 2)))ˣ) (hud : (ud : ZMod (2 ^ (e + 2))) = (d : ZMod _)) (g : FrobeniusOrbits.GG e) :
    (∃ k : ℕ, g.1.1 = (-1) ^ k ∧ g.2 = hcl e ud ^ k) ↔ ∃ (u : (ZMod (2 ^ (e + 2) * q * d))ˣ) (k : ℕ),
    (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ d ^ k [MOD 2 ^ (e + 2) * q] ∧ g = art0 e hH u := by sorry
