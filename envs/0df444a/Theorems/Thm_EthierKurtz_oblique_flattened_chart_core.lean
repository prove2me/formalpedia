-- Prove2me | Theorems.Thm_EthierKurtz_oblique_flattened_chart_core
-- name    : EthierKurtz.oblique_flattened_chart_core
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-28T22:34:16.378849+00:00
-- url     : https://prove2.me/theorems/7de1c0da-4611-4e05-8e4f-90c9f01bfec4
-- title:
--   Flattened chart core from the shear extension
-- statement:
--   From the shear package of the statement, the shear map is a local $C^{2,\mu}$ diffeomorphism flattening the boundary near the base point, with quantitative inverse bounds: $$\|x-x'\|\le2\|\Theta x-\Theta x'\|.$$
--
--   Role: second half of the chart construction.
-- source:
--   D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, https://doi.org/10.1007/978-3-642-61798-0, Section 6.2 (straightening the boundary); used in Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Section 1

import Mathlib
import Definitions.Def_EthierKurtz_CTwiceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_COnceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
open MeasureTheory Real Set Filter
open scoped Topology

namespace EthierKurtz

theorem oblique_flattened_chart_core (n : ℕ) (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hS : ∀ {m : ℕ} (w : Fin m → EuclideanSpace ℝ (Fin (n + 1))) (e : EuclideanSpace ℝ (Fin (n + 1))) (he : ‖e‖ = 1)
    (M0 M1 H : Fin m → ℝ) (ψ : Fin m → EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (ψ1 : Fin m → EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ))
    (hd : ∀ i y, HasFDerivAt (ψ i) (ψ1 i y) y) (hc : ∀ i, Continuous (ψ1 i))
    (hb0 : ∀ i y, |ψ i y| ≤ M0 i) (hb1 : ∀ i y, ‖ψ1 i y‖ ≤ M1 i)
    (hhol : ∀ i y z, ‖ψ1 i y - ψ1 i z‖ ≤ H i * ‖y - z‖ ^ μ) (hH : ∀ i, 0 ≤ H i),
    ∃ (Gm : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) (DG : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))) (D2G : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))),
      (∀ x v, (∀ i, inner ℝ (w i) v = 0) → inner ℝ (Gm x) v = inner ℝ x v) ∧
      (∀ x, HasStrictFDerivAt Gm (DG x) x) ∧ Continuous DG ∧
      (∀ x, inner ℝ x e = 0 → Gm x = x ∧
        DG x = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + 1))) - (innerSL ℝ e).smulRight (∑ i, ψ i x • w i)) ∧
      (∀ x, 0 < inner ℝ x e → HasFDerivAt DG (D2G x) x) ∧
      (∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 ≤ r → ∃ K, let S : Set (EuclideanSpace ℝ (Fin (n + 1))) := {x : EuclideanSpace ℝ (Fin (n + 1)) | 0 ≤ inner ℝ x e ∧ dist x c ≤ r}
        0 ≤ K ∧ (∀ x ∈ S, ∀ y ∈ S, ‖Gm x - Gm y‖ ≤ K * ‖x - y‖) ∧ (∀ x ∈ S, ‖DG x‖ ≤ K) ∧ (∀ x ∈ S, ∀ y ∈ S, ‖DG x - DG y‖ ≤ K * ‖x - y‖) ∧ (∀ x ∈ S, ‖D2G x‖ ≤ K) ∧ (∀ x ∈ S, ∀ y ∈ S, ‖D2G x - D2G y‖ ≤ K * ‖x - y‖ ^ μ))) :
    let eL : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single (Fin.last n) 1
    let gr : (EuclideanSpace ℝ (Fin n) → ℝ) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + 1)) := fun u z => WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i))
    let Fl : (EuclideanSpace ℝ (Fin n) → ℝ) → EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) := fun u ξ => ξ - u (WithLp.toLp 2 (fun i => ξ (Fin.castSucc i))) • eL
    ∀ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))), IsOpen Ω → ∀ (x0 : EuclideanSpace ℝ (Fin (n + 1))) (U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (Du : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (D2u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (R K : ℝ), 0 < R →
    (0 ≤ K ∧ (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖u x - u y‖ ≤ K * ‖x - y‖) ∧
      (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖Du x‖ ≤ K) ∧ (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖Du x - Du y‖ ≤ K * ‖x - y‖) ∧
      (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖D2u x‖ ≤ K) ∧ (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖D2u x - D2u y‖ ≤ K * ‖x - y‖ ^ μ)) →
    (∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, HasFDerivAt u (Du z) z ∧ HasFDerivAt Du (D2u z) z) →
    u 0 = 0 → Du 0 = 0 → ∀ (c : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))),
    (∀ k, ∃ (M0 M1 H : ℝ) (f1 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ),
      (∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, HasFDerivAt (fun z => U (c (x0 + U.symm (gr u z))) k) (f1 y) y) ∧
      (∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, |U (c (x0 + U.symm (gr u y))) k| ≤ M0) ∧ (∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖f1 y‖ ≤ M1) ∧
      (∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖f1 y - f1 z‖ ≤ H * ‖y - z‖ ^ μ) ∧ 0 ≤ H) →
    ∀ (s r1 : ℝ), (s = 1 ∨ s = -1) → 0 < r1 →
    (∀ x ∈ Metric.ball x0 r1, (x ∈ Ω ↔ 0 < -s * inner ℝ (Fl u (U (x - x0))) eL) ∧
      (x ∈ frontier Ω ↔ inner ℝ (Fl u (U (x - x0))) eL = 0)) →
    0 < s * U (c x0) (Fin.last n) →
    ∃ (r0 K : ℝ) (e b : EuclideanSpace ℝ (Fin (n + 1)))
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
