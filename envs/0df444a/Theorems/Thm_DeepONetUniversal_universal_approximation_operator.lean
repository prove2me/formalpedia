-- Prove2me | Theorems.Thm_DeepONetUniversal_universal_approximation_operator
-- name    : DeepONetUniversal.universal_approximation_operator
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T08:34:13.033131+00:00
-- url     : https://prove2.me/theorems/eff18484-48a9-4d79-850c-6989ee087f0e
-- title:
--   Theorem 1: universal approximation theorem for operators
-- statement:
--   Let $\sigma$ be a continuous function that is not a polynomial, $X$ a Banach space, $K_1\subset X$ a nonempty compact set, $K_2\subset\mathbb{R}^d$ compact, $V\subset C(K_1)$ compact, and $G:V\to C(K_2)$ a (possibly nonlinear) continuous operator. Then for every $\varepsilon>0$ there are positive integers $n,p,m$, constants $c_i^k,\xi_{ij}^k,\theta_i^k,\zeta_k\in\mathbb{R}$, $w_k\in\mathbb{R}^d$ and sensors $x_j\in K_1$ ($i=1,\dots,n$, $k=1,\dots,p$, $j=1,\dots,m$) such that
--
--   $$\Big|G(u)(y)-\sum_{k=1}^p\underbrace{\sum_{i=1}^nc_i^k\,\sigma\Big(\sum_{j=1}^m\xi_{ij}^ku(x_j)+\theta_i^k\Big)}_{\text{branch}}\underbrace{\sigma(w_k\cdot y+\zeta_k)}_{\text{trunk}}\Big|<\varepsilon$$
--
--   for all $u\in V$ and $y\in K_2$.
--
--   This is the universal approximation theorem for operators of Chen and Chen (1995) on which the DeepONet architecture is built: the sum is a stacked DeepONet with $p$ branch networks and one trunk network.
--
--   **Formalization Note** $G$ is a map on all of $C(K_1)$ that is continuous on $V$; its values off $V$ play no role. The hypothesis $K_1\neq\emptyset$ is added: the conclusion asks for $m\ge1$ sensors in $K_1$, which is impossible when $K_1$ is empty.
-- source:
--   Lu, Jin and Karniadakis, DeepONet: Learning nonlinear operators for identifying differential equations based on the universal approximation theorem of operators, arXiv:1910.03193v3 (2019), Section 1, Theorem 1, eq. (1), p. 2

import Mathlib
import Definitions.Def_DeepONetUniversal_Basic

open MeasureTheory Filter Topology

namespace DeepONetUniversal

theorem universal_approximation_operator {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] {d : ℕ} (σ : ℝ → ℝ) (hσc : Continuous σ) (hσp : ¬ IsPolynomialFun σ)
    (K₁ : Set X) (hK₁ : IsCompact K₁) (hK₁ne : K₁.Nonempty)
    (K₂ : Set (Fin d → ℝ)) (hK₂ : IsCompact K₂)
    (V : Set C(K₁, ℝ)) (hV : IsCompact V) (G : C(K₁, ℝ) → C(K₂, ℝ)) (hG : ContinuousOn G V)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n p m : ℕ, 0 < n ∧ 0 < p ∧ 0 < m ∧
      ∃ (c : Fin p → Fin n → ℝ) (ξ : Fin p → Fin n → Fin m → ℝ) (θ : Fin p → Fin n → ℝ)
        (ζ : Fin p → ℝ) (w : Fin p → Fin d → ℝ) (x : Fin m → K₁),
        ∀ u ∈ V, ∀ y : K₂, |G u y - operatorNet σ c ξ θ w ζ (fun j => u (x j)) y| < ε := by sorry

end DeepONetUniversal
