-- Prove2me | Theorems.Thm_FiniteEnergyPlane_halfCyl_coeff_bounds
-- name    : FiniteEnergyPlane.halfCyl_coeff_bounds
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-28T22:40:04.836507+00:00
-- url     : https://prove2.me/theorems/75ebd162-7f4f-42d8-b598-59b642c1d0ee
-- title:
--   Eventual coefficient bounds for a matrix field converging in $C^\infty$ on a half-cylinder
-- statement:
--   Let $S:\mathbb{R}\times\mathbb{R}\to\mathbb{R}^{2n\times2n}$ be smooth, and let $S_\infty:\mathbb{R}\to\mathbb{R}^{2n\times2n}$ be a smooth symmetric $1$-periodic loop. Suppose $S(s,t)\to S_\infty(t)$ in $C^\infty$ as $s\to+\infty$, entrywise and uniformly in $t$. Then there are $s_0>0$ and $c$ such that for all $s\ge s_0$, all $t$ and all entries $(i,j)$,
--   $$|S_{ij}(s,t)|\le c,\qquad|\partial_sS_{ij}(s,t)|\le c,\qquad|\partial_s^2S_{ij}(s,t)|\le c.$$
--
--   So the coefficients of the linear Cauchy–Riemann operator $\partial_s+J_0\partial_t+S$, and their first two $s$-derivatives, are uniformly bounded far out on the half-cylinder.
--
--   **Formalization Note** The convergence is `IsCInftyAsymptoticTo S Sinf`. The $s$-derivatives are written as `fderiv ℝ (fun p => S p i j) (s, t) (1, 0)` and `fderiv ℝ (fun p => fderiv ℝ (fun q => S q i j) p (1, 0)) (s, t) (1, 0)`.
-- source:
--   Used for C. Wendl, Lectures on Symplectic Field Theory (2026 notes), Lemma 4.8.8

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real RealInnerProductSpace

/-- If `S(s, t) → S∞(t)` in `C^∞` with `S∞` a smooth symmetric loop, then for large `s` the entries
of `S`, `∂ₛS` and `∂ₛ²S` are bounded by a fixed constant. -/
theorem halfCyl_coeff_bounds {n : ℕ} (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hSas : IsCInftyAsymptoticTo S Sinf) :
    ∃ s₀ c : ℝ, 0 < s₀ ∧ ∀ s ≥ s₀, ∀ t : ℝ, ∀ i j, |S (s, t) i j| ≤ c ∧
      |fderiv ℝ (fun p : ℝ × ℝ => S p i j) (s, t) (1, 0)| ≤ c ∧
      |fderiv ℝ (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => S q i j) p (1, 0)) (s, t) (1, 0)| ≤
        c := by
  sorry

end FiniteEnergyPlane
