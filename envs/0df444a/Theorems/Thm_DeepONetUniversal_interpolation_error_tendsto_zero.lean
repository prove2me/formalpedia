-- Prove2me | Theorems.Thm_DeepONetUniversal_interpolation_error_tendsto_zero
-- name    : DeepONetUniversal.interpolation_error_tendsto_zero
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T08:35:53.126011+00:00
-- url     : https://prove2.me/theorems/4a378ddb-4bbf-40a2-8a2a-8db7e33da566
-- title:
--   Eq. (4): the interpolation error κ(m, V) tends to zero
-- statement:
--   Let $a<b$ and let $V$ be a compact subset of $C[a,b]$. For $m\ge1$ let $u_m=\mathcal L_m(u)$ be the piecewise-linear interpolant of $u$ at the uniform sensors $x_j=a+j(b-a)/m$, $j=0,\dots,m$. Then there are constants $\kappa(m,V)$ such that
--
--   $$\max_{x\in[a,b]}|u(x)-u_m(x)|\le\kappa(m,V)\quad\text{for all }u\in V,\ m\ge1,\qquad\kappa(m,V)\to0\ \text{as }m\to\infty.$$
--
--   The constant $\kappa(m,V)$ enters the sensor count of Theorem 2.
--
--   **Formalization Note** The paper asserts eq. (4) without proof; it is stated here as an existence claim for a sequence $\kappa(\cdot,V)$ with both properties.
-- source:
--   Lu, Jin and Karniadakis, DeepONet: Learning nonlinear operators for identifying differential equations based on the universal approximation theorem of operators, arXiv:1910.03193v3 (2019), Section 3, eq. (4), p. 6

import Mathlib
import Definitions.Def_DeepONetUniversal_Basic

open MeasureTheory Filter Topology

namespace DeepONetUniversal

theorem interpolation_error_tendsto_zero {a b : ℝ} (hab : a < b) (V : Set C(Set.Icc a b, ℝ))
    (hV : IsCompact V) :
    ∃ κ : ℕ → ℝ,
      (∀ m : ℕ, 0 < m → ∀ u ∈ V, ∀ x ∈ Set.Icc a b, |evalAt u x - interp a b m (evalAt u) x| ≤ κ m) ∧
        Tendsto κ atTop (𝓝 0) := by sorry

end DeepONetUniversal
