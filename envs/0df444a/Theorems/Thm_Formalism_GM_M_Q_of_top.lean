-- Prove2me | Theorems.Thm_Formalism_GM_M_Q_of_top
-- name    : Formalism.GM.M.Q_of_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:57.726071+00:00
-- url     : https://prove2.me/theorems/0a0ce3fc-786d-4879-b1ba-8ae499235f24
-- title:
--   M: Q of top
-- statement:
--   The M construction uses the Q of top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L633-L641
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L633-L641

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

theorem Formalism.GM.M.Q_of_top (j : Fin D.T.t → ℕ) (jp : ℕ) (v : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hv : v ∈ Submodule.span ℚ_[p] (D.gens p (r := r) j jp)) (P : ℚ_[p] → Prop) (hP0 : P 0)
    (htop : ∀ m, sd (scalS N r D.T.t) m = lv j jp → P (coeff m v)) :
    ∃ Q ∈ Submodule.span ℚ_[p] (Bset (p := p) D j jp), v = pre D j jp * Q ∧ ∀ n, P (coeff n Q) := by sorry
