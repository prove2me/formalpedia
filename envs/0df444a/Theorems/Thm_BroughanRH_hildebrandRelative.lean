-- Prove2me | Theorems.Thm_BroughanRH_hildebrandRelative
-- name    : BroughanRH.hildebrandRelative
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:28:02.146619+00:00
-- url     : https://prove2.me/theorems/ebdd3cd3-895e-4632-8b22-79576044da54
-- title:
--   Hildebrand’s relative smooth-number estimate
-- statement:
--   In the alternative range $(\log x)^{2+\varepsilon}\le y\le x$ with $y\ge2$, Hildebrand gives the additive relative-error form with the same Dickman function and a uniform constant.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II Thm. 13.18 (alternative form). https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem hildebrandRelative :
    let Ψ (x y : ℝ) := ((Finset.Icc 1 ⌊x⌋₊).filter fun n => ∀ p : ℕ, p ∈ n.primeFactors → (p : ℝ) ≤ y).card
    ∃ ρ : ℝ → ℝ, ContinuousOn ρ (Set.Ici 0) ∧ (∀ u ∈ Set.Icc 0 1, ρ u = 1) ∧
      (∀ u : ℝ, 1 < u → HasDerivAt ρ (-ρ (u-1) / u) u) ∧
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ,
        2 ≤ y → y ≤ x → (Real.log x)^(2+ε) ≤ y →
        let u := Real.log x / Real.log y
        ∃ e : ℝ, |e| ≤ C * Real.log (u+1) / Real.log y ∧
          (Ψ x y : ℝ) = x * ρ u * (1+e) := by sorry

end BroughanRH
