-- Prove2me | Theorems.Thm_EdenVerified_D10_kaplan_yorke_convention
-- name    : EdenVerified.D10_kaplan_yorke_convention
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:26:53.882799+00:00
-- url     : https://prove2.me/theorems/e16ba19e-33f3-5533-971d-6e7b76caf18a
-- title:
--   Eden Verified: D10 kaplan yorke convention
-- statement:
--   The largest nonnegative partial-sum index, including its endpoint branches.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L624-L641
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L624-L641

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.D10_kaplan_yorke_convention (a : Fin 5 → ℝ) :
    spectrumPartialSum a 0 = 0 ∧
    kaplanYorkeDimension a ∈ Icc 0 5 ∧
    (∀ k : ℕ, spectrumPartialSum a k = ∑ i ∈ Finset.range k, spectrumEntry a i) ∧
    (kaplanYorkeIndex a ≤ 5 ∧ 0 ≤ spectrumPartialSum a (kaplanYorkeIndex a)) ∧
    (∀ k : ℕ, k ≤ 5 → 0 ≤ spectrumPartialSum a k → k ≤ kaplanYorkeIndex a) ∧
    (kaplanYorkeIndex a = 0 → kaplanYorkeDimension a = 0) ∧
    (kaplanYorkeIndex a = 5 → kaplanYorkeDimension a = 5) ∧
    (0 < kaplanYorkeIndex a → kaplanYorkeIndex a < 5 →
      spectrumEntry a (kaplanYorkeIndex a) < 0 ∧
      kaplanYorkeDimension a = (kaplanYorkeIndex a : ℝ) +
        spectrumPartialSum a (kaplanYorkeIndex a) / |spectrumEntry a (kaplanYorkeIndex a)|) := by sorry
