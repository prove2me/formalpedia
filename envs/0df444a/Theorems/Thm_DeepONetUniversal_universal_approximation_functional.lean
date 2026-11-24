-- Prove2me | Theorems.Thm_DeepONetUniversal_universal_approximation_functional
-- name    : DeepONetUniversal.universal_approximation_functional
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T08:32:56.832719+00:00
-- url     : https://prove2.me/theorems/6266c56b-c9eb-4f41-9490-00f202896b4b
-- title:
--   Theorem 4: universal approximation theorem for functionals
-- statement:
--   Let $\sigma$ be a Tauber–Wiener function, $X$ a Banach space, $K\subset X$ compact, $V\subset C(K)$ compact, and $f$ a continuous functional on $V$. Then for every $\varepsilon>0$ there are a positive integer $n$, points $x_1,\dots,x_m\in K$ and real constants $c_i,\theta_i,\xi_{ij}$ ($i=1,\dots,n$, $j=1,\dots,m$) such that
--
--   $$\Big|f(u)-\sum_{i=1}^nc_i\,\sigma\Big(\sum_{j=1}^m\xi_{ij}u(x_j)+\theta_i\Big)\Big|<\varepsilon\quad\text{for all }u\in V.$$
--
--   This is the branch-network half of the operator theorem (Chen and Chen, 1995).
--
--   **Formalization Note** Continuity of $f$ is continuity on $V$ (the paper's Definition 2 asks for uniform continuity, which is equivalent on the compact set $V$).
-- source:
--   Lu, Jin and Karniadakis, DeepONet: Learning nonlinear operators for identifying differential equations based on the universal approximation theorem of operators, arXiv:1910.03193v3 (2019), Appendix A, Theorem 4, p. 19

import Mathlib
import Definitions.Def_DeepONetUniversal_Basic

open MeasureTheory Filter Topology

namespace DeepONetUniversal

theorem universal_approximation_functional {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (σ : ℝ → ℝ) (hσ : IsTauberWiener σ)
    (K : Set X) (hK : IsCompact K) (V : Set C(K, ℝ)) (hV : IsCompact V)
    (f : C(K, ℝ) → ℝ) (hf : ContinuousOn f V) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ (m : ℕ) (x : Fin m → K) (c θ : Fin n → ℝ) (ξ : Fin n → Fin m → ℝ),
      ∀ u ∈ V, |f u - branchNet σ c ξ θ (fun j => u (x j))| < ε := by sorry

end DeepONetUniversal
