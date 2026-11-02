-- Prove2me | Theorems.Thm_EthierKurtz_oblique_coefficient_extension_to_closure
-- name    : EthierKurtz.oblique_coefficient_extension_to_closure
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-02T00:13:11.452966+00:00
-- url     : https://prove2.me/theorems/82dde5f6-4e26-4400-893f-dc6bd1df91cb
-- title:
--   Hoelder coefficients extend to the closure of a domain with flattening charts
-- statement:
--   Let $\Omega$ be open, $0<\mu$, with boundary flattening charts at every boundary point. If the entries of $a$ and $b$ are $\mu$-Hoelder on the components of $\Omega\cap B$ in the sense of ComponentHolder, $a$ is positive semidefinite on $\Omega$ and uniformly elliptic ($\varepsilon\le\theta^\top a(x)\theta$ for unit $\theta$), then there are $\bar a,\bar b$ with $\bar a=a$, $\bar b=b$ on $\Omega$, locally bounded and locally $\mu$-Hoelder near every point of $\overline\Omega$, and $\bar a(x)$ positive definite for every $x\in\overline\Omega$.
--
--   Role: makes the coefficients of the parent defined and Hoelder up to the boundary, so the frozen-coefficient construction applies at boundary points.
-- source:
--   D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, https://doi.org/10.1007/978-3-642-61798-0, Section 4.1 and Lemma 6.37 (extension of Hoelder functions to the closure of a $C^{k,\alpha}$ domain); used in Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Theorem 1.5 and its proof (p. 369)

import Mathlib
import Definitions.Def_EthierKurtz_CTwiceHolder
import Definitions.Def_EthierKurtz_ComponentHolder
open MeasureTheory Real Set Filter
open scoped Topology
open scoped BoundedContinuousFunction

namespace EthierKurtz

theorem oblique_coefficient_extension_to_closure (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩ : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ)
    (c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hch : ∀ x0 ∈ frontier Ω, ∃ (r0 K : ℝ) (e b : EuclideanSpace ℝ (Fin d))
        (Θ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        (DΘ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
        (D2Θ : EuclideanSpace ℝ (Fin d) →
          EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
        0 < r0 ∧ ‖e‖ = 1 ∧ inner ℝ b e = 0 ∧
        (∀ x ∈ Metric.ball x0 r0, HasStrictFDerivAt Θ (DΘ x) x) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ Ω, HasFDerivAt DΘ (D2Θ x) x) ∧
        Θ x0 = 0 ∧ DΘ x0 = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) ∧
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
          ‖D2Θ x - D2Θ y‖ ≤ K * ‖x - y‖ ^ μ))
    (a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (haH : ∀ i j, EthierKurtz.ComponentHolder Ω μ (fun x => a x i j))
    (hbH : ∀ i, EthierKurtz.ComponentHolder Ω μ (fun x => b x i))
    (ha : ∀ x ∈ Ω, (a x).PosSemidef)
    (hell : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Ω, ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ = 1 → ε ≤ ∑ i, ∑ j, θ i * a x i j * θ j) :
    ∃ (abar : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (bbar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
      (∀ x ∈ Ω, abar x = a x ∧ bbar x = b x) ∧
      (∀ x0 ∈ closure Ω, ∃ R Ka : ℝ, 0 < R ∧
        (∀ x ∈ Metric.ball x0 R ∩ closure Ω, ∑ i, ∑ j, |abar x i j| ≤ Ka ∧ ‖bbar x‖ ≤ Ka) ∧
        (∀ x ∈ Metric.ball x0 R ∩ closure Ω, ∀ x' ∈ Metric.ball x0 R ∩ closure Ω,
          ∑ i, ∑ j, |abar x i j - abar x' i j| ≤ Ka * ‖x - x'‖ ^ μ ∧ ‖bbar x - bbar x'‖ ≤ Ka * ‖x - x'‖ ^ μ)) ∧
      (∀ x ∈ closure Ω, (abar x).PosDef) := by sorry

end EthierKurtz
