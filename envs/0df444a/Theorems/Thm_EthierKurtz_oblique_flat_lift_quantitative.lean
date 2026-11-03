-- Prove2me | Theorems.Thm_EthierKurtz_oblique_flat_lift_quantitative
-- name    : EthierKurtz.oblique_flat_lift_quantitative
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-02T04:29:10.581611+00:00
-- url     : https://prove2.me/theorems/25f26add-d8b0-4ddb-aa17-4ea37fe3f39a
-- title:
--   Flat lift of C^{1,mu} normal-derivative data with C^2 bounds linear in the C^1 size of the data
-- statement:
--   Let $0<\mu\le1$. There is $K_0\ge0$ such that every compactly supported $C^1$ function $q$ on $\mathbb R^n$ with $\mu$-Hoelder gradient and $|q|\le S$, $\|Dq\|\le S$ has a compactly supported $C^1$ lift $W$ on $\mathbb R^n\times\mathbb R$ with $W(z,0)=0$, $DW(z,0)=q(z)\,dt$, $W\in C^2$ on $\{t>0\}$ with $\mu$-Hoelder $D^2W$ there, and
--   $$|W|\le K_0S,\qquad \|DW\|\le K_0S,\qquad \|D^2W(p)\|\le K_0S\ \ (t>0).$$
--
--   Role: the quantitative version of the flat lifting step: the size of the corrector is controlled by the $C^1$ size of the boundary datum, which tends to zero along the approximating sequence.
-- source:
--   D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, https://doi.org/10.1007/978-3-642-61798-0, Section 6.7 (Lemma 6.38 and the lifting of boundary values by variable-radius mollification); used in Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Theorem 1.5 and its proof (p. 369)

import Mathlib
open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

theorem oblique_flat_lift_quantitative (n : ℕ) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ q : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 q → HasCompactSupport q →
      (∃ M : ℝ, ∀ x y, ‖fderiv ℝ q x - fderiv ℝ q y‖ ≤ M * ‖x - y‖ ^ μ) →
      ∀ S : ℝ, (∀ z, |q z| ≤ S) → (∀ z, ‖fderiv ℝ q z‖ ≤ S) →
      ∃ W : EuclideanSpace ℝ (Fin n) × ℝ → ℝ,
        ContDiff ℝ 1 W ∧ HasCompactSupport W ∧
        ContDiffOn ℝ 2 W {p | 0 < p.2} ∧
        (∀ z, W (z, 0) = 0) ∧
        (∀ z, fderiv ℝ W (z, 0) = q z • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ) ∧
        (∀ p, |W p| ≤ K₀ * S) ∧ (∀ p, ‖fderiv ℝ W p‖ ≤ K₀ * S) ∧
        (∀ p : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 → ‖fderiv ℝ (fderiv ℝ W) p‖ ≤ K₀ * S) ∧
        ∃ K : ℝ, ∀ p p' : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 → 0 < p'.2 →
          ‖fderiv ℝ (fderiv ℝ W) p - fderiv ℝ (fderiv ℝ W) p'‖ ≤ K * ‖p - p'‖ ^ μ := by sorry

end EthierKurtz
