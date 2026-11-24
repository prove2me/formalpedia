-- Prove2me | Theorems.Thm_DeepONetUniversal_number_of_sensors
-- name    : DeepONetUniversal.number_of_sensors
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T08:37:35.490927+00:00
-- url     : https://prove2.me/theorems/fef24e43-05b3-411c-810e-1f51c821f7c8
-- title:
--   Theorem 2 (as proved): number of sensors for identifying nonlinear dynamic systems
-- statement:
--   Let $a<b$, let $V$ be a compact subset of $C[a,b]$ and let $W\supset V$ be the compact set of Lemma 7. Let $\sigma$ be continuous and not a polynomial. Let $G$ map each $u\in W$ to the solution $s=Gu\in C([a,b];\mathbb{R}^K)$ of
--
--   $$\frac{d}{dx}s(x)=g(s(x),u(x),x),\qquad s(a)=s_0,$$
--
--   in the integral form $(Gu)(x)=s_0+\int_a^xg((Gu)(t),u(t),t)\,dt$, and let $G$ be continuous on $W$. Suppose that for some $c>0$, $g$ satisfies $\|g(s_1,u,x)-g(s_2,u,x)\|_2\le c\|s_1-s_2\|_2$ and $\|g(s,u_1,x)-g(s,u_2,x)\|_2\le c|u_1-u_2|$ for all values $s,s_1,s_2$ of functions in $G(W)$, all values $u,u_1,u_2$ of functions in $W$, and $x\in[a,b]$. Let $m\ge1$ and let $\kappa$ bound the interpolation error, $\max_{x\in[a,b]}|u(x)-u_m(x)|\le\kappa$ for all $u\in V$. If
--
--   $$c(b-a)\,\kappa\,e^{c(b-a)}<\varepsilon,$$
--
--   then for every $d\in[a,b]$ there are $n$, $W_1\in\mathbb{R}^{n\times(m+1)}$, $b_1\in\mathbb{R}^n$, $W_2\in\mathbb{R}^{K\times n}$, $b_2\in\mathbb{R}^K$ such that
--
--   $$\big\|(Gu)(d)-\big(W_2\,\sigma(W_1[u(x_0)\ \cdots\ u(x_m)]^T+b_1)+b_2\big)\big\|_2<\varepsilon\quad\text{for all }u\in V.$$
--
--   The number of sensors needed for accuracy $\varepsilon$ is thus governed by the interpolation error $\kappa(m,V)$ of the input space.
--
--   **Formalization Note** The paper prints $b_1\in\mathbb{R}^{m+1}$; the bias of $n$ hidden units lies in $\mathbb{R}^n$. The paper leaves $\sigma$ unspecified; the hypothesis of Theorem 1 (continuous, not a polynomial) is used, which is what the universal approximation theorem invoked in the proof requires. "Lipschitz on $G(W)\times W$" is read as Lipschitz on the values of these functions. The integrability of $t\mapsto g((Gu)(t),u(t),t)$ on $[a,b]$ is the implicit condition under which the integral equation is meaningful. $\kappa$ is any bound on the interpolation error at this $m$, which is the role of $\kappa(m,V)$ in eq. (4).
-- source:
--   Lu, Jin and Karniadakis, DeepONet: Learning nonlinear operators for identifying differential equations based on the universal approximation theorem of operators, arXiv:1910.03193v3 (2019), Section 3, Theorem 2, eqs. (3)-(4), pp. 5-6; proof in Appendix B, pp. 20-21

import Mathlib
import Definitions.Def_DeepONetUniversal_Basic

open MeasureTheory Filter Topology

namespace DeepONetUniversal

theorem number_of_sensors {a b : ℝ} (hab : a < b) {K : ℕ} (σ : ℝ → ℝ) (hσc : Continuous σ)
    (hσp : ¬ IsPolynomialFun σ) (V : Set C(Set.Icc a b, ℝ)) (hV : IsCompact V)
    (g : (Fin K → ℝ) → ℝ → ℝ → (Fin K → ℝ)) (s₀ : Fin K → ℝ)
    (G : C(Set.Icc a b, ℝ) → C(Set.Icc a b, Fin K → ℝ))
    (hG : SolvesODE a b g s₀ G (sensorHull a b V)) (hGc : ContinuousOn G (sensorHull a b V))
    (c : ℝ) (hc : 0 < c)
    (hL : IsLipschitzSU a b g c (valueSet (G '' sensorHull a b V)) (valueSet (sensorHull a b V)))
    (m : ℕ) (hm : 0 < m) (κ : ℝ)
    (hκ : ∀ u ∈ V, ∀ x ∈ Set.Icc a b, |evalAt u x - interp a b m (evalAt u) x| ≤ κ)
    (ε : ℝ) (hε : c * (b - a) * κ * Real.exp (c * (b - a)) < ε) (d : Set.Icc a b) :
    ∃ (n : ℕ) (W₁ : Matrix (Fin n) (Fin (m + 1)) ℝ) (b₁ : Fin n → ℝ) (W₂ : Matrix (Fin K) (Fin n) ℝ)
      (b₂ : Fin K → ℝ),
      ∀ u ∈ V, eucNorm (G u d - shallowNet σ W₁ b₁ W₂ b₂ (sensorValues a b m u)) < ε := by sorry

end DeepONetUniversal
