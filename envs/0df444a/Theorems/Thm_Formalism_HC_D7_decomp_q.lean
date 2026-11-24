-- Prove2me | Theorems.Thm_Formalism_HC_D7_decomp_q
-- name    : Formalism.HC.D7.decomp_q
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:39:58.318383+00:00
-- url     : https://prove2.me/theorems/815b30eb-e0a7-4005-9524-faeca31d4c0d
-- title:
--   D7: decomp q
-- statement:
--   The D7 construction uses the decomp q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ArtinMapSecondEqJacobiSymOfModEq.lean#L332-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ArtinMapSecondEqJacobiSymOfModEq.lean#L332-L350

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

theorem Formalism.HC.D7.decomp_q (uq : (ZMod (2 ^ (e + 2)))ˣ) (huq : (uq : ZMod (2 ^ (e + 2))) = (q : ZMod _)) (g : FrobeniusOrbits.GG e) :
    (g.1.2 = 1 ∧ ∃ k : ℕ, g.2 = hcl e uq ^ k) ↔ ∃ (u : (ZMod (2 ^ (e + 2) * q * d))ˣ) (k : ℕ),
    (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ q ^ k [MOD 2 ^ (e + 2) * d] ∧ g = art0 e hH u := by sorry
