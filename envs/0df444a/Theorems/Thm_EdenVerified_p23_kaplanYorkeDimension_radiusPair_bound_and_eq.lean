-- Prove2me | Theorems.Thm_EdenVerified_p23_kaplanYorkeDimension_radiusPair_bound_and_eq
-- name    : EdenVerified.p23_kaplanYorkeDimension_radiusPair_bound_and_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:51:34.495466+00:00
-- url     : https://prove2.me/theorems/b25bb506-9165-5ed0-9102-f820c4247ef7
-- title:
--   Eden Verified: p23 kaplan Yorke Dimension radius Pair bound and eq
-- statement:
--   The Eden Verified construction uses the p23 kaplan Yorke Dimension radius Pair bound and eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1790-L1796
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1790-L1796

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p23_kaplanYorkeDimension_radiusPair_bound_and_eq :
    ∀ {c s₁ s₂ : ℝ} (hc : 4 < c)
    (hs₁ : s₁ = 0 ∨ s₁ = 1 ∨ s₁ = 2) (hs₂ : s₂ = 0 ∨ s₂ = 1 ∨ s₂ = 2),
    kaplanYorkeDimension (descending (radiusPairSpectrum c s₁ s₂)) ≤ targetDimension c ∧
      (kaplanYorkeDimension (descending (radiusPairSpectrum c s₁ s₂)) = targetDimension c ↔
        s₁ = 1 ∧ s₂ = 1) := by sorry
