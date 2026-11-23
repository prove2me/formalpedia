-- Prove2me | Theorems.Thm_BroughanRH_hildebrand
-- name    : BroughanRH.hildebrand
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:27:57.868825+00:00
-- url     : https://prove2.me/theorems/45c1cbc7-3779-4ace-8a5f-6be74d4109cb
-- title:
--   Hildebrand’s exponential estimate for smooth numbers
-- statement:
--   For $y\ge2$ and $1\le u\le y^{1/2-\varepsilon}$, the count of $y$-smooth integers through $y^u$ equals $y^u\rho(u)\exp(O_\varepsilon(\log(u+1)/\log y))$. The initial values and delay differential equation specify Dickman’s function.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II Thm. 13.18. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem hildebrand :
    let Ψ (x y : ℝ) := ((Finset.Icc 1 ⌊x⌋₊).filter fun n => ∀ p : ℕ, p ∈ n.primeFactors → (p : ℝ) ≤ y).card
    ∃ ρ : ℝ → ℝ, ContinuousOn ρ (Set.Ici 0) ∧ (∀ u ∈ Set.Icc 0 1, ρ u = 1) ∧
      (∀ u : ℝ, 1 < u → HasDerivAt ρ (-ρ (u-1) / u) u) ∧
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ y u : ℝ,
        2 ≤ y → 1 ≤ u → u ≤ y^(1/2-ε) → ∃ e : ℝ,
          |e| ≤ C * Real.log (u+1) / Real.log y ∧
          (Ψ (y^u) y : ℝ) = y^u * ρ u * Real.exp e := by sorry

end BroughanRH
