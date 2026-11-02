-- Prove2me | Theorems.Thm_EthierKurtz_oblique_boundary_datum_c1_vanishing
-- name    : EthierKurtz.oblique_boundary_datum_c1_vanishing
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-02T04:30:02.315955+00:00
-- url     : https://prove2.me/theorems/82621a0a-1146-47e6-b980-b246782bf132
-- title:
--   The oblique boundary datum of C^2 approximations tends to zero in C^1 along a boundary chart
-- statement:
--   Let $J$ be continuous on $\overline\Omega$ with $J(y)c(y)=0$ on $\partial\Omega$, $X$ a $C^1$ map from an open set $O\supseteq\overline B(0,r)$ into $\partial\Omega$ with $c\circ X\in C^1$, $\zeta\in C^1$, and $F_k\in C^2$ with $\|DF_k-J\|\le\eta_k$ and $\|D^2F_k-D^2F_l\|\le\eta_k+\eta_l$ on $\Omega$, where $\eta_k\to0$. Then $Q_k(z)=\zeta(Xz)\,DF_k(Xz)\,c(Xz)$ satisfies
--   $$\sup_{\overline B(0,r)}|Q_k|\to0,\qquad \sup_{\overline B(0,r)}\|DQ_k\|\to0.$$
--
--   Role: shows that the boundary data the correctors must cancel become small in $C^1$, so the corrections vanish in $C^2$ in the limit.
-- source:
--   W. Rudin, Principles of Mathematical Analysis, 3rd ed., McGraw-Hill, 1976, Theorem 7.17 (uniform convergence and differentiation); used in Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Theorem 1.5 and its proof (p. 369)

import Mathlib
open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

theorem oblique_boundary_datum_c1_vanishing (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (c : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (J : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ))
    (hJ : ContinuousOn J (closure Ω)) (hJc : ∀ y ∈ frontier Ω, J y (c y) = 0)
    (X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + 1)))
    (O : Set (EuclideanSpace ℝ (Fin n))) (hO : IsOpen O) (r : ℝ) (hr0 : 0 < r)
    (hr : Metric.closedBall 0 r ⊆ O) (hX : ContDiffOn ℝ 1 X O)
    (hcX : ContDiffOn ℝ 1 (fun z => c (X z)) O) (hXf : ∀ z ∈ O, X z ∈ frontier Ω)
    (ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (hζ : ContDiff ℝ 1 ζ)
    (F : ℕ → EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (hF : ∀ k, ContDiff ℝ 2 (F k)) (η : ℕ → ℝ)
    (hη : Tendsto η atTop (𝓝 0))
    (h1 : ∀ k, ∀ y ∈ Ω, ‖fderiv ℝ (F k) y - J y‖ ≤ η k)
    (h2 : ∀ k l, ∀ y ∈ Ω,
      ‖fderiv ℝ (fderiv ℝ (F k)) y - fderiv ℝ (fderiv ℝ (F l)) y‖ ≤ η k + η l) :
    ∀ δ > 0, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r,
      |ζ (X z) * fderiv ℝ (F k) (X z) (c (X z))| ≤ δ ∧
      ‖fderiv ℝ (fun z => ζ (X z) * fderiv ℝ (F k) (X z) (c (X z))) z‖ ≤ δ := by sorry

end EthierKurtz
