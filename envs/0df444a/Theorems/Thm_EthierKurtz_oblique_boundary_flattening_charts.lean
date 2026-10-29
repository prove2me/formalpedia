-- Prove2me | Theorems.Thm_EthierKurtz_oblique_boundary_flattening_charts
-- name    : EthierKurtz.oblique_boundary_flattening_charts
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-28T21:52:22.198961+00:00
-- url     : https://prove2.me/theorems/8dab1fd0-5ee0-40d3-b320-46abd70d4a6e
-- title:
--   Flattening charts for a $C^{2,\mu}$ boundary with an oblique field
-- statement:
--   Let $\Omega\subset\mathbb{R}^{n+1}$ be open with $C^{2,\mu}$ boundary, $c$ a $C^{1,\mu}$ oblique field and $0<\mu<1$. Given the extension package of the statement, every boundary point has a $C^{2,\mu}$ chart $\Theta$ flattening $\partial\Omega$ to a hyperplane, with $D\Theta(x_0)=I$ and the oblique field transported as in the statement: $$\Theta(\Omega\cap B)=\{\langle z,e\rangle>0\}\cap\Theta(B).$$
--
--   Role: the localisation charts.
-- source:
--   D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, https://doi.org/10.1007/978-3-642-61798-0, Section 6.2 (flattening the boundary) and Section 6.7; used in Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Section 1

import Mathlib
import Definitions.Def_EthierKurtz_CTwiceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_COnceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
open MeasureTheory Real Set Filter
open scoped Topology

namespace EthierKurtz

theorem oblique_boundary_flattening_charts (n : ℕ) (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hP : ∀ (M0 M1 H : ℝ) (ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (ψ1 : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)) (e : EuclideanSpace ℝ (Fin (n + 1))),
        (∀ y, HasFDerivAt ψ (ψ1 y) y) → Continuous ψ1 → (∀ y, |ψ y| ≤ M0) → (∀ y, ‖ψ1 y‖ ≤ M1) →
        (∀ y z, ‖ψ1 y - ψ1 z‖ ≤ H * ‖y - z‖ ^ μ) → 0 ≤ H → ‖e‖ = 1 →
        ∃ (E : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (DE : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)) (D2E : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)),
          (∀ x, HasStrictFDerivAt E (DE x) x) ∧ Continuous DE ∧
          (∀ x, inner ℝ x e = 0 → E x = 0 ∧ DE x = ψ x • innerSL ℝ e) ∧
          (∀ x, 0 < inner ℝ x e → HasFDerivAt DE (D2E x) x) ∧
          ∃ C, 0 ≤ C ∧ ∀ x x' : EuclideanSpace ℝ (Fin (n + 1)), 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
            ‖D2E x' - D2E x‖ ≤ C * ‖x' - x‖ ^ μ)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) (hΩ : IsOpen Ω) (hboundary : EthierKurtz.BoundaryCTwiceHolder Ω μ)
    (c ν : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (hc : ∀ i, EthierKurtz.BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, EthierKurtz.IsOutwardUnitNormal Ω x (ν x))
    (hobl : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω, ε ≤ ∑ i, c x i * ν x i) :
    ∀ x0 ∈ frontier Ω, ∃ (r0 K : ℝ) (e b : EuclideanSpace ℝ (Fin (n + 1)))
            (Θ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
            (DΘ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
            (D2Θ : EuclideanSpace ℝ (Fin (n + 1)) →
              EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))),
            0 < r0 ∧ ‖e‖ = 1 ∧ inner ℝ b e = 0 ∧
            (∀ x ∈ Metric.ball x0 r0, HasStrictFDerivAt Θ (DΘ x) x) ∧
            (∀ x ∈ Metric.ball x0 r0 ∩ Ω, HasFDerivAt DΘ (D2Θ x) x) ∧
            Θ x0 = 0 ∧ DΘ x0 = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + 1))) ∧
            (∀ x ∈ Metric.ball x0 r0,
              (x ∈ Ω ↔ 0 < inner ℝ (Θ x) e) ∧ (x ∈ frontier Ω ↔ inner ℝ (Θ x) e = 0)) ∧
            (∀ x ∈ Metric.ball x0 r0 ∩ frontier Ω, ∃ κ : ℝ, 0 < κ ∧ DΘ x (c x) = κ • (b - e)) ∧
            0 ≤ K ∧
            (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∀ y ∈ Metric.ball x0 r0 ∩ closure Ω,
              ‖Θ x - Θ y‖ ≤ K * ‖x - y‖) ∧
            (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ‖DΘ x‖ ≤ K) ∧
            (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∀ y ∈ Metric.ball x0 r0 ∩ closure Ω,
              ‖DΘ x - DΘ y‖ ≤ K * ‖x - y‖) ∧
            (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ‖D2Θ x‖ ≤ K) ∧
            (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∀ y ∈ Metric.ball x0 r0 ∩ closure Ω,
              ‖D2Θ x - D2Θ y‖ ≤ K * ‖x - y‖ ^ μ) := by sorry

end EthierKurtz
