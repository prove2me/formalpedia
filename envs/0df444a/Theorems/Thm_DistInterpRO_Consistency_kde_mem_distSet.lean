-- Prove2me | Theorems.Thm_DistInterpRO_Consistency_kde_mem_distSet
-- name    : DistInterpRO.Consistency.kde_mem_distSet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:48:09.849988+00:00
-- url     : https://prove2.me/theorems/41397aeb-2cfe-4689-af45-185e76550f4e
-- title:
--   Proof of Theorem 3.1 — the box kernel density estimator is the density of a member of $\mathcal P_n$
-- statement:
--   Let $n\ge1$, $\epsilon>0$ and $x_1,\dots,x_n\in\mathbb R^m$. Let $\mathcal Z_i=\{x_i+\delta\mid\|\delta\|_\infty\le\epsilon\}$ and let
--   $$h_n(x)=(n\epsilon^m)^{-1}\sum_{i=1}^nK\Big(\frac{x-x_i}{\epsilon}\Big),\qquad K(z)=\frac{\mathbf 1(\|z\|_\infty\le1)}{2^m}.$$
--   Then the measure $\mu_n$ with Lebesgue density $h_n$ is a probability measure on $\mathbb R^m$ and, for every $S\subseteq\{1,\dots,n\}$,
--   $$\int_{\mathbb R^m}\mathbf 1\Big(x\in\bigcup_{j\in S}\mathcal Z_j\Big)h_n(x)\,dx\ \ge\ \frac{|S|}{n},$$
--   that is, $\mu_n\in\mathcal P_n$.
--
--   This is the step of the proof of Theorem 3.1 that places a kernel density estimator inside the distribution set of the robust problem (footnote 2: "$h_n$ is the density function of a probability measure that belongs to $\mathcal P_n$").
--
--   **Formalization Note** The measure is `volume.withDensity (ofReal ∘ hₙ)` on `Fin m → ℝ` with the sup norm; membership in $\mathcal P_n$ includes being a probability measure, which is where the normalisation $2^m$ of $K$ is used. The paper states this for the bandwidth $\epsilon(n)$; the statement holds for every $\epsilon>0$.
-- source:
--   Xu, Caramanis and Mannor, A Distributional Interpretation of Robust Optimization, Math. Oper. Res. 37(1) (2012), p. 99, proof of Theorem 3.1, the display chain at the top of the page ending '= |S|/n' and the sentence 'Hence, hₙ ∈ 𝒫ₙ' with footnote 2

import Mathlib
import Definitions.Def_DistInterpRO_Consistency_Model

open MeasureTheory Filter Topology ProbabilityTheory

namespace DistInterpRO.Consistency

theorem kde_mem_distSet {m n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε)
    (xs : Fin n → Fin m → ℝ) :
    volume.withDensity (fun x => ENNReal.ofReal (kde ε xs x)) ∈
      distSet (fun i => box (xs i) ε) := by sorry

end DistInterpRO.Consistency
