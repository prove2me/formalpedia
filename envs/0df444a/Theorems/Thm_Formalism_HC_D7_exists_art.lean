-- Prove2me | Theorems.Thm_Formalism_HC_D7_exists_art
-- name    : Formalism.HC.D7.exists_art
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:40:14.195809+00:00
-- url     : https://prove2.me/theorems/c4614df2-03fe-46a5-8f60-d3d872d154e6
-- title:
--   D7: exists art
-- statement:
--   The D7 construction uses the exists art property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ArtinMapSecondEqJacobiSymOfModEq.lean#L202-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ArtinMapSecondEqJacobiSymOfModEq.lean#L202-L231

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

theorem Formalism.HC.D7.exists_art (g : FrobeniusOrbits.GG e) (x y z : ℕ) (v : (ZMod (2 ^ (e + 2)))ˣ)
    (hv : (v : ZMod (2 ^ (e + 2))) = (x : ZMod (2 ^ (e + 2)))) (hx : g.2 = hcl e v)
    (hy : ((g.1.1 : ℤˣ) : ℤ) = jacobiSym (y : ℤ) q) (hz : ((g.1.2 : ℤˣ) : ℤ) = jacobiSym (z : ℤ) d) :
    ∃ u : (ZMod (2 ^ (e + 2) * q * d))ˣ, (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ x [MOD 2 ^ (e + 2)] ∧
      (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ y [MOD q] ∧ (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ z [MOD d] ∧
      g = art0 e hH u := by sorry
