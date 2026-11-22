-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_tubeCoords_near_linearized
-- name    : FiniteEnergyPlane.exists_tubeCoords_near_linearized
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-21T13:02:36.614304+00:00
-- url     : https://prove2.me/theorems/07048b70-b907-4b92-969d-d29933d2e6f3
-- title:
--   Reeb trajectories near a periodic orbit follow the linearized flow in tube coordinates
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$ be strictly star-shaped, with a $d\lambda_0$-compatible complex structure $J$ on $\xi$. Let $P = (x, T)$ be a periodic Reeb orbit, $Z$ a unitary frame of $\xi$ along $P$, and $S_\infty$ the symmetric loop representing the asymptotic operator in this frame. Consider the tube map $(\tau, a) \mapsto \mathrm{proj}(x(\tau) + Z(\tau/T)\,a)$, with $\tau \in \mathbb{R}$ and $a \in \mathbb{R}^2$. Fix $L > 0$.
--
--   Then there is a constant $C$ with the following property. For every $\varepsilon > 0$ there is an open set $W \supseteq x(\mathbb{R})$ such that each Reeb trajectory $y$ with $y(0) \in W$ admits the following data:
--   - tube coordinates $y(0) = \mathrm{proj}(x(\tau_0) + Z(\tau_0/T)\,a_0)$ with $|a_0| < \varepsilon$, and $a_0 \ne 0$ when $y(0) \notin x(\mathbb{R})$;
--   - a solution $\zeta$ of $\zeta' = J_0 S_\infty(t)\,\zeta$ with $\zeta(\tau_0/T) = a_0$;
--   - continuous functions $\tau, a$ on $[-L, L]$ with $y(\sigma) = \mathrm{proj}(x(\tau(\sigma)) + Z(\tau(\sigma)/T)\,a(\sigma))$.
--
--   Moreover, for all $\sigma \in [-L, L]$:
--   $$|\tau(\sigma) - \tau_0 - \sigma| \le C|a_0|, \qquad |a_0| \le C\,|\zeta((\tau_0+\sigma)/T)|, \qquad |\zeta((\tau_0+\sigma)/T)| \le C|a_0|, \qquad |a(\sigma) - \zeta((\tau_0+\sigma)/T)| \le C|a_0|^2.$$
--
--   Role: over a fixed time window, Reeb trajectories near $P$ follow the linearized Reeb flow along $P$ to second order in tube coordinates.
--
--   Formalization Note: `IsReebTrajectory H y` means $y(t) \in S$ and $y' = R(y)$ for all $t$. `hA` is the frame representation of the asymptotic operator supplied by `FiniteEnergyPlane.asympOp_frame_bridge`.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6.2 (proof of Lemma 6.9); H. Hofer, K. Wysocki, E. Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), Section 5

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Near the orbit, Reeb trajectories in the tube `(τ, a) ↦ proj H (x(τ) + Z(τ/T) a)` stay
quadratically close, over a fixed time window, to solutions of the linearized equation. -/
theorem exists_tubeCoords_near_linearized (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)
    (Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hZ : IsUnitaryXiFrame J P Z)
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSym : CauchyRiemannIndex.IsSymLoop Sinf)
    (hA : ∀ η : ℝ → CauchyRiemannIndex.Vec 1, ContDiff ℝ ∞ η → Function.Periodic η 1 →
        ∀ t : ℝ, asympOp J P (fun t => Z t (η t)) t =
          Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv η t)) -
            Matrix.toEuclideanLin (Sinf t) (η t)))
    (L : ℝ) (hL : 0 < L) :
    ∃ C : ℝ, ∀ ε > 0, ∃ W : Set (V 1), IsOpen W ∧ Set.range P.x ⊆ W ∧
      ∀ y : ℝ → V 1, IsReebTrajectory H y → y 0 ∈ W →
        ∃ (τ₀ : ℝ) (a₀ : CauchyRiemannIndex.Vec 1) (τ : ℝ → ℝ)
          (a ζ : ℝ → CauchyRiemannIndex.Vec 1),
          ‖a₀‖ < ε ∧ (y 0 ∉ Set.range P.x → a₀ ≠ 0) ∧
          (∀ t : ℝ, HasDerivAt ζ
            (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * Sinf t) (ζ t)) t) ∧
          ζ (τ₀ / P.T) = a₀ ∧
          ContinuousOn τ (Set.Icc (-L) L) ∧ ContinuousOn a (Set.Icc (-L) L) ∧
          ∀ σ ∈ Set.Icc (-L) L,
            y σ = proj H (P.x (τ σ) + Z (τ σ / P.T) (a σ)) ∧
            |τ σ - τ₀ - σ| ≤ C * ‖a₀‖ ∧
            ‖a₀‖ ≤ C * ‖ζ ((τ₀ + σ) / P.T)‖ ∧ ‖ζ ((τ₀ + σ) / P.T)‖ ≤ C * ‖a₀‖ ∧
            ‖a σ - ζ ((τ₀ + σ) / P.T)‖ ≤ C * ‖a₀‖ ^ 2 := by
  sorry

end FiniteEnergyPlane
