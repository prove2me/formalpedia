-- Prove2me | Theorems.Thm_EdenVerified_attractor_lemma
-- name    : EdenVerified.attractor_lemma
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:19:56.001775+00:00
-- url     : https://prove2.me/theorems/6ac3b9f8-825c-5b90-b998-a017b536a33d
-- title:
--   Eden Verified: attractor lemma
-- statement:
--   Manuscript Lemma `lem:attractor`, with the paper's parameter assumption.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L101-L111
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L101-L111

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.attractor_lemma (c : ℝ) (hc : 4 < c) :
    (∀ p : PhaseSpace, ∃ f : ℝ → PhaseSpace, f 0 = p ∧
      ∀ t : ℝ, 0 ≤ t → HasDerivAt f (vectorField c (f t)) t) ∧
    attractor.Nonempty ∧ IsCompact attractor ∧
    (∀ t : ℝ, 0 ≤ t → evolution c t '' attractor = attractor) ∧
    (∀ B : Set PhaseSpace, Bornology.IsBounded B → ∀ ε : ℝ, 0 < ε →
      ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → ∀ p ∈ B,
        ∃ q ∈ attractor, dist (evolution c t p) q < ε) := by sorry
