-- Prove2me | Theorems.Thm_BesbesZeevi_Parametric_lemma1
-- name    : BesbesZeevi.Parametric.lemma1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:18:12.723169+00:00
-- url     : https://prove2.me/theorems/e37e9ef9-ac28-422b-95ea-14abfec979b7
-- title:
--   Lemma 1 — solution of the deterministic relaxation
-- statement:
--   Let $p^u(\theta)$ maximize $p\lambda(p;\theta)$ and let $p^c(\theta)$ minimize $|\lambda(p;\theta)-x/T|$ on the admissible price interval. Put $p^D(\theta)=\max\{p^u(\theta),p^c(\theta)\}$. For every $\theta\in\Theta$,
--
--   $$J^D(x,T\mid\theta)=p^D(\theta)\lambda(p^D(\theta);\theta)\min\left\{T,\frac{x}{\lambda(p^D(\theta);\theta)}\right\}.$$
--
--   The path that posts $p^D(\theta)$ up to $T'=\min\{T,x/\lambda(p^D(\theta);\theta)\}$ and then posts $p_\infty$ is feasible and attains this benchmark. **Formalization Note** This item formalizes the first assertion of Lemma 1. The separate upper bound on arbitrary adaptive policies is not included.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 27 (PDF p. 29), Lemma 1, first assertion

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_Algorithm

namespace BesbesZeevi.Parametric

/-- The optimal deterministic price path in the first assertion of Lemma 1, p. 27. -/
theorem lemma1 {k : ℕ} (D : Market) (F : Family k D) :
    ∀ θ ∈ F.Θ, ∀ pu pc : ℝ,
      pu ∈ Set.Icc D.pLo D.pHi →
      pc ∈ Set.Icc D.pLo D.pHi →
      (∀ p ∈ Set.Icc D.pLo D.pHi,
        p * F.demand p θ ≤ pu * F.demand pu θ) →
      (∀ p ∈ Set.Icc D.pLo D.pHi,
        |F.demand pc θ - D.x / D.T| ≤ |F.demand p θ - D.x / D.T|) →
      let cutoff := min D.T (D.x / F.demand (max pu pc) θ)
      let path : ℝ → ℝ := fun t => if t ≤ cutoff then max pu pc else D.pOff
      DetFeasible D (fun p => F.demand p θ) D.x path ∧
        jDet D (fun p => F.demand p θ) D.x =
          max pu pc * F.demand (max pu pc) θ * cutoff := by sorry

end BesbesZeevi.Parametric
