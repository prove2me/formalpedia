-- Prove2me | Theorems.Thm_Formalism_GM_M_ss_sat
-- name    : Formalism.GM.M.ss_sat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:28.793804+00:00
-- url     : https://prove2.me/theorems/1d24d862-3933-4de9-97bf-2a3c203ab833
-- title:
--   M: ss sat
-- statement:
--   The M construction uses the ss sat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L748-L778
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L748-L778

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

theorem Formalism.GM.M.ss_sat (x : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hx : x ∈ Submodule.span ℚ_[p] (D.SSZ p (r := r) : Set (MvPolynomial (BVar N r D.T.t) ℚ_[p])))
    (hi : x ∈ IntPol p (BVar N r D.T.t)) : x ∈ D.SSZ p (r := r) := by sorry
