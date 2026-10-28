-- Prove2me | Theorems.Thm_EthierKurtz_oblique_flat_lift
-- name    : EthierKurtz.oblique_flat_lift
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-25T05:14:24.639971+00:00
-- url     : https://prove2.me/theorems/902b3432-d504-485d-882f-5bbfa825fa83
-- title:
--   Flat lift of C^{1,mu} normal-derivative data to a C^{2,mu} function on a half-space
-- statement:
--   Let $0<\mu\le 1$ and let $q:\mathbb{R}^n\to\mathbb{R}$ be a compactly supported $C^1$ function whose gradient is $\mu$-Hoelder. For every $\delta>0$ there is a compactly supported $C^1$ function $W$ on $\mathbb{R}^n\times\mathbb{R}$ with $|W|\le\delta$, $W(z,0)=0$ and $DW(z,0)=q(z)\,dt$ (so $\partial_t W(z,0)=q(z)$ and $\nabla_z W(z,0)=0$), which is $C^2$ on the open half-space $\{t>0\}$ with $D^2W$ uniformly $\mu$-Hoelder there:
--   $$\|D^2W(p)-D^2W(p')\|\le K\,|p-p'|^{\mu}\qquad (p,p'\in\{t>0\}).$$
--
--   Role: in the parent, this is the local lifting step that produces functions satisfying the oblique boundary condition: in a boundary chart one adds a lift of the prescribed normal-derivative data to a smooth approximation.
--
--   **Formalization Note**: $W$ is built as $W(z,t)=\psi(t)\int_{|y|\le1}q(z-ty)\eta(y)\,dy$ with $\psi(t)=t\chi(t)$ a small cutoff and $\eta$ a normalized bump; only the half-space $\{t>0\}$ is controlled, since the domain lies on one side of its boundary in each chart.
-- source:
--   D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, Section 6.7 (Lemma 6.38 and the lifting of boundary values by variable-radius mollification); used in Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Section 1

import Mathlib

namespace EthierKurtz

theorem oblique_flat_lift (n : ℕ) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1)
    (q : EuclideanSpace ℝ (Fin n) → ℝ) (hq : ContDiff ℝ 1 q) (hqs : HasCompactSupport q)
    (hqH : ∃ M : ℝ, ∀ x y, ‖fderiv ℝ q x - fderiv ℝ q y‖ ≤ M * ‖x - y‖ ^ μ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ W : EuclideanSpace ℝ (Fin n) × ℝ → ℝ,
      ContDiff ℝ 1 W ∧ HasCompactSupport W ∧
      ContDiffOn ℝ 2 W {p | 0 < p.2} ∧
      (∀ z, W (z, 0) = 0) ∧
      (∀ z, fderiv ℝ W (z, 0) = q z • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ) ∧
      (∀ p, |W p| ≤ δ) ∧
      ∃ K : ℝ, ∀ p p' : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 → 0 < p'.2 →
        ‖fderiv ℝ (fderiv ℝ W) p - fderiv ℝ (fderiv ℝ W) p'‖ ≤ K * ‖p - p'‖ ^ μ := by sorry

end EthierKurtz
