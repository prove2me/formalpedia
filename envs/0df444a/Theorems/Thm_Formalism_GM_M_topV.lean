-- Prove2me | Theorems.Thm_Formalism_GM_M_topV
-- name    : Formalism.GM.M.topV
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:13:12.93391+00:00
-- url     : https://prove2.me/theorems/6ce118a5-29cc-49a0-be0f-1e0b3b2d4def
-- title:
--   M: top V
-- statement:
--   The M construction uses the top V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L623-L631
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L623-L631

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M
open MvPolynomial Finset SSD
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero r] (D : BlockData N)

theorem Formalism.GM.M.topV (j : Fin D.T.t → ℕ) (jp : ℕ) (v : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hv : v ∈ Submodule.span ℚ_[p] (D.gens p (r := r) j jp)) :
    ∃ s Q, Q ∈ Submodule.span ℚ_[p] (Bset (p := p) D j jp) ∧ v = pre D j jp * Q ∧
      sd (scalS N r D.T.t) s = lv j jp ∧ (∀ m ∈ v.support, sd (scalS N r D.T.t) m ≤ lv j jp) ∧
      ∀ n, coeff (s + n) v = coeff n Q := by sorry
