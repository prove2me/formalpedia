-- Prove2me | Theorems.Thm_Formalism_GM_M_xi_mono
-- name    : Formalism.GM.M.xi_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:56.186195+00:00
-- url     : https://prove2.me/theorems/a827846e-2d18-48fb-b333-f6c6bdad7d50
-- title:
--   M: xi mono
-- statement:
--   The M construction uses the xi mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L579-L584
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L579-L584

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

theorem Formalism.GM.M.xi_mono {b : ℕ} {g : MvPolynomial (BVar N r D.T.t) ℚ_[p]} (hg : g ∈ XiPolZ p N r D.T.t b)
    {m : BVar N r D.T.t →₀ ℕ} (hm : m ∈ g.support) :
    (∀ v ∈ m.support, ∃ c, v = xiVar N r D.T.t c) ∧ ∑ c, m (xiVar N r D.T.t c) = b := by sorry
