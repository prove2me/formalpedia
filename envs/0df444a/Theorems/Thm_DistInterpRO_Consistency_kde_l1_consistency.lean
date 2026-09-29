-- Prove2me | Theorems.Thm_DistInterpRO_Consistency_kde_l1_consistency
-- name    : DistInterpRO.Consistency.kde_l1_consistency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:50:10.035467+00:00
-- url     : https://prove2.me/theorems/50b7fb96-e438-4b31-8a98-ba90cea02afa
-- title:
--   Strong $L^1$ consistency of the box kernel density estimator (Devroye–Györfi), as used in the proof of Theorem 3.1
-- statement:
--   Let $h^*$ be a probability density on $\mathbb R^m$ (nonnegative, Lebesgue integrable, $\int h^*=1$), and let $X_1,X_2,\dots$ be independent random vectors on a probability space $(\Omega,\mathcal F,\mathbb P)$, each with distribution $h^*(x)\,dx$. Let $\epsilon(n)>0$ be bandwidths with
--   $$\epsilon(n)\to0\qquad\text{and}\qquad n\,\epsilon(n)^m\to\infty,$$
--   and let $h_n$ be the kernel density estimator built from $X_1,\dots,X_n$ with the uniform box kernel $K(z)=\mathbf 1(\|z\|_\infty\le1)/2^m$ and bandwidth $\epsilon(n)$. Then, with probability one,
--   $$\int_{\mathbb R^m}|h_n(x)-h^*(x)|\,dx\ \xrightarrow{\,n\to\infty\,}\ 0.$$
--
--   This is a known theorem that the paper cites and uses without proof ("it is well known (e.g., see Devroye and Györfi [15])"); it is the probabilistic input to Theorem 3.1. It is the strong $L^1$ consistency of kernel density estimates (Devroye 1983; Devroye and Györfi 1985), which holds for **every** density $h^*$, with no continuity or support assumption.
--
--   **Formalization Note** The samples are $X_0,X_1,\dots$ in Lean (index shifted by one), and $h_n$ uses the first $n$ of them. Independence is `iIndepFun` and identical distribution is `P.map Xᵢ = volume.withDensity h*`. The $L^1$ distance is a Bochner integral; $h_n-h^*$ is integrable. No monotonicity of $\epsilon(n)$ or of $n\epsilon(n)^m$ is assumed: the paper states this step with limits only.
-- source:
--   Xu, Caramanis and Mannor, A Distributional Interpretation of Robust Optimization, Math. Oper. Res. 37(1) (2012), p. 99, proof of Theorem 3.1, the paragraph 'Since hₙ is a kernel density estimator, it is well known (e.g., see Devroye and Györfi [15]) …'; restated in Appendix A, p. 108

import Mathlib
import Definitions.Def_DistInterpRO_Consistency_Model

open MeasureTheory Filter Topology ProbabilityTheory

namespace DistInterpRO.Consistency

theorem kde_l1_consistency {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hstar : (Fin m → ℝ) → ℝ) (hstar_nonneg : ∀ x, 0 ≤ hstar x)
    (hstar_int : Integrable hstar) (hstar_one : ∫ x, hstar x = 1)
    (X : ℕ → Ω → Fin m → ℝ) (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = volume.withDensity (fun x => ENNReal.ofReal (hstar x)))
    (ε : ℕ → ℝ) (hε_pos : ∀ n, 0 < ε n) (hε_lim : Tendsto ε atTop (𝓝 0))
    (hnε_lim : Tendsto (fun n : ℕ => (n : ℝ) * ε n ^ m) atTop atTop) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ∫ x, |kde (ε n) (fun i : Fin n => X i ω) x - hstar x|)
      atTop (𝓝 0) := by sorry

end DistInterpRO.Consistency
