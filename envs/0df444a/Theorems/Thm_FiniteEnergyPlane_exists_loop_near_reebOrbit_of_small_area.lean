-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_loop_near_reebOrbit_of_small_area
-- name    : FiniteEnergyPlane.exists_loop_near_reebOrbit_of_small_area
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-03T16:23:50.137749+00:00
-- url     : https://prove2.me/theorems/eb3afc82-795d-49bf-a8ef-c1342f63f626
-- title:
--   Long finite-energy cylinders of small area are close to periodic orbits
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $C,e,\eta>0$, suppose every periodic Reeb orbit of period at most $C$ is nondegenerate, and that $e$ is smaller than every such period and than every difference of two distinct such periods. Then for every $m\in\mathbb{N}$ and $\varepsilon>0$ there is $h>0$ with the following property. Let $R>0$ and let $u$ be a finite-energy $\tilde J$-holomorphic curve on $\{|z|>R\}$ with
--   - $E(u)\le C$ and $\int_{\{|z|>R\}}u^*d\lambda\le e$,
--   - $\int_{|z|=\rho}u^*\lambda\ge\eta$ for every counterclockwise circle of radius $\rho>R$.
--
--   Then for every $\rho\ge Re^{2\pi h}$ there are a periodic orbit $(x,T)$ with $T\le C$ and a phase $c$ such that the loop $t\mapsto\mathrm{proj}(u(\rho e^{2\pi it}))$ and $t\mapsto x(Tt+c)$ differ by at most $\varepsilon$ in $C^m$: all derivatives of order $\le m$ differ by at most $\varepsilon$ at every $t$.
--
--   **Formalization Note** $h$ depends only on $C,e,\eta,m,\varepsilon$ (it is chosen before $R$ and $u$). In cylindrical coordinates $z=e^{2\pi(s+it)}$ the condition $\rho\ge Re^{2\pi h}$ is $s\ge r+h$ with $R=e^{2\pi r}$. Compared with Hryniewicz's Lemma 4.11, no convergence of $u(s,\cdot)$ as $s\to\infty$ is assumed, and the neighbourhood of the orbits is the explicit $C^m$-$\varepsilon$ one.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 4.11; H. Hofer, K. Wysocki, E. Zehnder, Finite energy cylinders of small area, Ergodic Theory Dynam. Systems 22 (2002), 1451–1486, doi:10.1017/S0143385702001013, Theorem 1.1

import Definitions.Def_FiniteEnergyPlane_Compactness

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), Lemma 4.11; Hofer–Wysocki–Zehnder (ETDS 2002), Theorem 1.1. Fix
`C, e, η > 0` such that every periodic Reeb orbit of period at most `C` is nondegenerate, and `e` is
smaller than each such period and than each difference of two distinct such periods. Then for all
`m` and `ε > 0` there is `h > 0` with the following property. If `u` is a finite-energy
`J̃`-holomorphic curve on `{|z| > R}` with energy at most `C`, `dλ`-energy at most `e`, and action
`∫_{|z| = ρ} u*λ ≥ η` on every counterclockwise circle `|z| = ρ > R`, then for every
`ρ ≥ R e^{2πh}` the loop `t ↦ proj(u(ρ e^{2πit}))` is `C^m`-`ε`-close to `t ↦ x(Tt + c)` for some
periodic orbit `(x, T)` with `T ≤ C` and some phase `c`. -/
theorem exists_loop_near_reebOrbit_of_small_area {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J)
    (C e η : ℝ) (hnd : ∀ Q : ReebOrbit H, Q.T ≤ C → Q.IsNondegenerate) (he : 0 < e)
    (he₁ : ∀ Q : ReebOrbit H, Q.T ≤ C → e < Q.T)
    (he₂ : ∀ Q₁ Q₂ : ReebOrbit H, Q₁.T ≤ C → Q₂.T ≤ C → Q₁.T ≠ Q₂.T → e < |Q₁.T - Q₂.T|)
    (hη : 0 < η) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ ∀ (R : ℝ) (u : ℂ → V n), 0 < R →
      IsFiniteEnergyCurve H J {z | R < ‖z‖} u →
      energy H {z | R < ‖z‖} u ≤ ENNReal.ofReal C →
      dlambdaEnergy H {z | R < ‖z‖} u ≤ ENNReal.ofReal e →
      (∀ ρ : ℝ, R < ρ → η ≤ loopAction H u (ccwLoop ρ)) →
      ∀ ρ : ℝ, R * Real.exp (2 * π * h) ≤ ρ →
        ∃ Q : ReebOrbit H, Q.T ≤ C ∧ ∃ c : ℝ, ∀ k ≤ m, ∀ t : ℝ,
          ‖iteratedDeriv k (loopInS H u (ccwLoop ρ)) t -
            iteratedDeriv k (fun t => Q.x (Q.T * t + c)) t‖ ≤ ε := by
  sorry

end FiniteEnergyPlane
