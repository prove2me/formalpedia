-- Prove2me | Theorems.Thm_BroughanRH_zagierOpen
-- name    : BroughanRH.zagierOpen
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:26:55.256388+00:00
-- url     : https://prove2.me/theorems/f4792beb-d731-4a68-b8ef-a55cd7d6c017
-- title:
--   Zagier’s horocycle length ratios for open sets
-- statement:
--   For an admissible nonempty open subset of the modular surface, the fraction of a closed horocycle in the set differs from its hyperbolic area fraction by $O(y^{3/4-\varepsilon})$. The hypotheses spell out the Mellin transform, its continuation, pointwise inversion and convergence on the shifted lines used on pp. 217–219.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II Thm. 10.21 (Mellin admissibility). https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem zagierOpen :
    ∀ U : Set (ℝ × ℝ), IsOpen U → U.Nonempty → (∀ p ∈ U, 0 < p.2) →
      (∀ x y : ℝ, 0 < y → ((x+1,y) ∈ U ↔ (x,y) ∈ U)) →
      (∀ x y : ℝ, 0 < y → ((-x/(x^2+y^2),y/(x^2+y^2)) ∈ U ↔ (x,y) ∈ U)) →
      let F := U.indicator (fun _ => (1 : ℝ))
      let C (y : ℝ) := ∫ x in (0 : ℝ)..1, F (x,y)
      let mean := (3/Real.pi) * (∫ x in (-(1/2 : ℝ))..(1/2 : ℝ),
        ∫ y in Set.Ici (Real.sqrt (1-x^2)), F (x,y)/y^2)
      ∀ M : ℂ → ℂ, MeromorphicOn M Set.univ →
        (∀ s : ℂ, 1 < s.re →
          let h (y : ℝ) := (C y : ℂ)*(y : ℂ)^(s-2)
          MeasureTheory.IntegrableOn h (Set.Ioi 0) ∧ M s = ∫ y in Set.Ioi (0 : ℝ), h y) →
        (∀ y : ℝ, 0 < y →
          let h (t : ℝ) := M (2+(t : ℂ)*Complex.I) * (y : ℂ)^(-1-(t : ℂ)*Complex.I)
          Filter.Tendsto (fun T : ℝ => (∫ t in (-T)..T, h t)/(2*(Real.pi : ℂ)))
            Filter.atTop (nhds (C y : ℂ))) →
        (∀ σ : ℝ, 1/4 < σ → σ < 1 →
          MeasureTheory.Integrable (fun t : ℝ => M ((σ : ℂ)+(t : ℂ)*Complex.I))) →
        ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0))
          (fun y : ℝ => C y - mean) (fun y : ℝ => y^(3/4-ε)) := by sorry

end BroughanRH
