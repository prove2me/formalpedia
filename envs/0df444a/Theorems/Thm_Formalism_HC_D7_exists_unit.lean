-- Prove2me | Theorems.Thm_Formalism_HC_D7_exists_unit
-- name    : Formalism.HC.D7.exists_unit
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:41:34.691051+00:00
-- url     : https://prove2.me/theorems/4b58e005-bc80-457d-afdc-ce4e2cedd1d3
-- title:
--   D7: exists unit
-- statement:
--   The D7 construction uses the exists unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ArtinMapSecondEqJacobiSymOfModEq.lean#L147-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ArtinMapSecondEqJacobiSymOfModEq.lean#L147-L172

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

theorem Formalism.HC.D7.exists_unit (x y z : ℕ) (hx : Nat.Coprime x (2 ^ (e + 2))) (hy : Nat.Coprime y q) (hz : Nat.Coprime z d) :
    ∃ u : (ZMod (2 ^ (e + 2) * q * d))ˣ, (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ x [MOD 2 ^ (e + 2)] ∧
      (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ y [MOD q] ∧ (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ z [MOD d] := by sorry
