-- Prove2me | Theorems.Thm_BroughanRH_yoshidaNondegenerate
-- name    : BroughanRH.yoshidaNondegenerate
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:27:53.977089+00:00
-- url     : https://prove2.me/theorems/55ad1bd1-9591-4784-b297-02538e587071
-- title:
--   Nondegeneracy on Yoshida’s completed interval spaces
-- statement:
--   For every $a>0$ the Weil form has trivial radical on the completion of Yoshida’s truncated periodic tests. A Cauchy representative whose pairing with every test tends to zero represents zero. The squared norm here is the sum of the $L^2$ squared norm and the Weil quadratic form. Comparing this norm with the finite-mode splitting of §11.6 is part of the proof.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II Thm. 11.23. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib
import Definitions.Def_ConnesRZ_weil_defs

namespace BroughanRH

theorem yoshidaNondegenerate :
    let Q (f g : ℝ → ℂ) := ConnesRZ.weilDistribution (ConnesRZ.conv f (ConnesRZ.starInv g))
    let K (a : ℝ) (f : ℝ → ℂ) := ∃ g : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) g ∧
      Function.Periodic g (2*a) ∧ f = (Set.Icc (-a) a).indicator g
    let E (f : ℝ → ℂ) := (∫ x : ℝ, ‖f x‖^2) + (Q f f).re
    ∀ a : ℝ, 0 < a → ∀ F : ℕ → ℝ → ℂ, (∀ n, K a (F n)) →
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n → |E (F m - F n)| < ε) →
      (∀ g : ℝ → ℂ, K a g → Filter.Tendsto (fun n : ℕ => Q (F n) g) Filter.atTop (nhds 0)) →
      Filter.Tendsto (fun n : ℕ => E (F n)) Filter.atTop (nhds 0) := by sorry

end BroughanRH
