-- Prove2me | Theorems.Thm_FD1D_DyadicMass_haarTermsAt_width_pos
-- name    : FD1D.DyadicMass.haarTermsAt_width_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:09:10.388872+00:00
-- url     : https://prove2.me/theorems/c080d662-8960-432b-a164-e60586da508d
-- title:
--   Dyadic Mass: haar Terms At width pos
-- statement:
--   The Dyadic Mass construction uses the haar Terms At width pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L740-L752
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L740-L752

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral

theorem FD1D.DyadicMass.haarTermsAt_width_pos
    {L : ℕ} (q : DyadicMass L) {a p : ℝ} (hp : 0 < p)
    {t : HaarTerm} (ht : t ∈ q.haarTermsAt a p) :
    0 < t.width := by sorry
