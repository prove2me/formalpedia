-- Prove2me | Theorems.Thm_Formalism_HN_ex_slopes
-- name    : Formalism.HN.ex_slopes
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:11.60979+00:00
-- url     : https://prove2.me/theorems/25ad5737-3029-4caf-a788-9d3994eb1ee8
-- title:
--   HN: ex slopes
-- statement:
--   The HN construction uses the ex slopes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Example.lean#L194-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Example.lean#L194-L226

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Example
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
open PolygonExample
local notation "ρx" => AddMonoidHom.id E2

theorem Formalism.HN.ex_slopes (n : ℕ) (s : Fin n → ℝ) (hn : n = 2) (hanti : Antitone s)
    (hpos : ∀ θ : ℝ, 0 < θ → (Finset.univ.filter (fun j => θ ≤ s j)).card = 0)
    (h0 : (Finset.univ.filter (fun j => (0 : ℝ) ≤ s j)).card = 1)
    (hsum : ∑ j, s j = - Real.log 2) :
    ∀ j : Fin n, s j = if (j : ℕ) = 0 then 0 else - Real.log 2 := by sorry
