-- Prove2me | Theorems.Thm_EthierKurtz_oblique_local_corrector_quantitative
-- name    : EthierKurtz.oblique_local_corrector_quantitative
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-02T04:29:41.390551+00:00
-- url     : https://prove2.me/theorems/7e2cfae7-8aca-4d74-9b1a-31c7dee1e80e
-- title:
--   Local oblique corrector at a boundary point with C^2 bounds linear in the boundary datum
-- statement:
--   Let $\Omega\subset\mathbb R^{n+1}$ be open, $0<\mu\le1$, $c$ a field whose components are $C^{1,\mu}$ in the boundary graph charts with $c\cdot\nu\ge\varepsilon>0$ on $\partial\Omega$, and assume the quantitative flat lift (hypothesis `hlift`). Then every $x_0\in\partial\Omega$ has $\rho>0$, a $C^2$ boundary parametrisation $X$ of $\partial\Omega$ on an open set $O\supseteq\overline B(0,r)$ with $c\circ X\in C^1$, and $K_1\ge0$ such that for smooth $F,\xi$ with $\operatorname{supp}\xi\subset B(x_0,\rho)$ and every $S$ bounding $Q(z)=\xi(X z)\,DF(Xz)\,c(Xz)$ and $DQ$ on $\overline B(0,r)$, there is a compactly supported $C^1$ function $V\in C^{2,\mu}(\Omega)$ with
--   $$DV\,c=-\xi\,DF\,c\ \text{on }\partial\Omega,\qquad |V|,\ \|DV\|\le K_1S,\qquad |\partial_i\partial_jV|\le K_1S\ \text{on }\Omega.$$
--
--   Role: cancels the oblique derivative of the smooth approximation in one boundary chart at a cost proportional to the size of the boundary datum.
-- source:
--   D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, https://doi.org/10.1007/978-3-642-61798-0, Section 6.7 (oblique derivative problem: local flattening and lifting of boundary data); used in Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Theorem 1.5 and its proof (p. 369)

import Mathlib
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_CTwiceHolder
open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

theorem oblique_local_corrector_quantitative (n : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1)
    (c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (hc : ∀ i, BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x))
    (hoblique : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω, ε ≤ ∑ i, c x i * normal x i)
    (hlift : ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ q : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 q →
      HasCompactSupport q →
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
          ‖fderiv ℝ (fderiv ℝ W) p - fderiv ℝ (fderiv ℝ W) p'‖ ≤ K * ‖p - p'‖ ^ μ) :
    ∀ x₀ ∈ frontier Ω, ∃ ρ : ℝ, 0 < ρ ∧
      ∃ X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + 1)), ∃ r : ℝ, 0 < r ∧
      ∃ O : Set (EuclideanSpace ℝ (Fin n)), IsOpen O ∧ Metric.closedBall 0 r ⊆ O ∧
      ContDiffOn ℝ 2 X O ∧ (∀ i, ContDiffOn ℝ 1 (fun z => c (X z) i) O) ∧
      (∀ z ∈ O, X z ∈ frontier Ω) ∧
      ∃ K1 : ℝ, 0 ≤ K1 ∧
      ∀ F ξ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ξ → tsupport ξ ⊆ Metric.ball x₀ ρ →
        ∀ S : ℝ, (∀ z ∈ Metric.closedBall 0 r,
            |ξ (X z) * fderiv ℝ F (X z) (c (X z))| ≤ S ∧
            ‖fderiv ℝ (fun z => ξ (X z) * fderiv ℝ F (X z) (c (X z))) z‖ ≤ S) →
          ∃ V : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
            ContDiff ℝ 1 V ∧ HasCompactSupport V ∧
            CTwiceHolder Ω μ V ∧
            (∀ x ∈ frontier Ω, fderiv ℝ V x (c x) = -(ξ x * fderiv ℝ F x (c x))) ∧
            (∀ x, |V x| ≤ K1 * S) ∧ (∀ x, ‖fderiv ℝ V x‖ ≤ K1 * S) ∧
            ∀ x ∈ Ω, ∀ i j : Fin (n + 1),
              |fderiv ℝ (fun y => fderiv ℝ V y (EuclideanSpace.single j 1)) x
                (EuclideanSpace.single i 1)| ≤ K1 * S := by sorry

end EthierKurtz
