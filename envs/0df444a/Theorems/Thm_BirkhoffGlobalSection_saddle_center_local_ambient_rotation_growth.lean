-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_saddle_center_local_ambient_rotation_growth
-- name    : BirkhoffGlobalSection.saddle_center_local_ambient_rotation_growth
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-28T03:05:24.315786+00:00
-- url     : https://prove2.me/theorems/e9957a98-1574-4c13-bb38-2e4a383b2faa
-- title:
--   Arbitrarily large ambient rotation on a long saddle-center segment
-- statement:
--   For every real threshold $R$, there are an open neighborhood $U$ of both equal-mass saddles $s_\pm=(\pm\tfrac12,0,0,0)$ and positive numbers $\varepsilon,\eta,L$ with the following property. Suppose
--
--   $$
--   0<\mu<1,\quad |\mu-\tfrac12|<\varepsilon,\quad c<2+\eta,\quad -c<h_1(\mu).
--   $$
--
--   Let $x$ be any complete Hamiltonian trajectory on the selected Levi–Civita component and $Y$ its identity-normalized variational flow. For every continuous ambient determinant angle $\alpha$ and every real $a$,
--
--   $$
--   x([a,a+L])\subset U\quad\Longrightarrow\quad\alpha(a+L)-\alpha(a)>R.
--   $$
--
--   The trajectory need not be periodic. The threshold and constants are independent of the initial time and variational direction. This separates the local saddle-center growth mechanism from all global and transverse-winding estimates.
--
--   **Formalization Note** This is the local normal-form growth consequence in the proof of Theorem 1.8, expressed for the Levi–Civita variational equation and the complex-linear determinant phase. Stability for nearby coefficients and arbitrary initial matrices is part of the obligation.
-- source:
--   Liu–Salomão, https://arxiv.org/html/2506.17867v2#S7, Eq. (7.7) and the final proof of Theorem 1.8 (local Hessian comparison and arbitrarily large index on a resident segment); Section 10 for the subcritical regime. Adapted to Levi–Civita coordinates and the determinant rotation map of Gutt, https://arxiv.org/pdf/1307.7239, Theorem 1, Eq. (3).

import Definitions.Def_BirkhoffGlobalSection_AmbientRotation

open scoped ContDiff

namespace BirkhoffGlobalSection

/-- A sufficiently long resident segment in small saddle-center charts has
arbitrarily large ambient determinant rotation. This is the local variational
estimate; no closed-orbit or complementary-arc conclusion is assumed. -/
theorem saddle_center_local_ambient_rotation_growth (R : ℝ) :
    ∃ U : Set Phase, IsOpen U ∧
      (![1 / 2, 0, 0, 0] : Phase) ∈ U ∧ (![-(1 / 2), 0, 0, 0] : Phase) ∈ U ∧
      ∃ ε η L : ℝ, 0 < ε ∧ 0 < η ∧ 0 < L ∧
        ∀ μ c : ℝ, 0 < μ → μ < 1 →
          |μ - 1 / 2| < ε → c < 2 + η → belowFirstCriticalValue μ c →
          ∀ x : ℝ → Phase,
            (∀ t : ℝ, x t ∈ leftEnergyComponent μ c) →
            (∀ t : ℝ, HasDerivAt x
              (hamiltonianVectorField (leviCivitaHamiltonian μ c) (x t)) t) →
            ∀ Y : ℝ → (Phase →L[ℝ] Phase),
              IsHamiltonianVariationalSolution (leviCivitaHamiltonian μ c) x Y →
              ∀ α : ℝ → ℝ, IsAmbientRotationAngle Y α →
                ∀ a : ℝ, (∀ t ∈ Set.Icc a (a + L), x t ∈ U) →
                  R < α (a + L) - α a := by sorry

end BirkhoffGlobalSection
