-- Prove2me | Theorems.Thm_Formalism_GM_M_gens_mem_SSZ
-- name    : Formalism.GM.M.gens_mem_SSZ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:38.172835+00:00
-- url     : https://prove2.me/theorems/59aceefe-a3bb-47a4-805d-4ca1eb799015
-- title:
--   M: gens mem SSZ
-- statement:
--   The M construction uses the gens mem SSZ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L658-L660
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L658-L660

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

theorem Formalism.GM.M.gens_mem_SSZ (j : Fin D.T.t → ℕ) (jp : ℕ) (hL : D.LevelOK j jp) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hx : x ∈ D.gens p (r := r) j jp) : x ∈ D.SSZ p (r := r) := by sorry
