-- Prove2me | Theorems.Thm_DistCov_Hilbert_gaussian_series
-- name    : DistCov.Hilbert.gaussian_series
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:27:52.440323+00:00
-- url     : https://prove2.me/theorems/85ce166a-d50d-4bc1-b776-1055acb99010
-- title:
--   p. 18 — Z(u) = Σ uₙZₙ converges ρ-a.s., is N(0, ‖u‖₂²), and E|Z(u)| = c‖u‖₂
-- statement:
--   Let $\rho$ be the law on $\mathbb R^\infty$ of an IID sequence of standard normal variables, $c=\mathbf E|Z_1|$, and for $w\in\mathbb R^\infty$ write $w(u)=\limsup_N\sum_{n=1}^N u_nw_n$. For every $u\in\ell^2(\mathbb Z^+)$:
--
--   1. for $\rho$-a.e. $w$ the series $\sum_n u_nw_n$ converges, to $w(u)$;
--   2. the law of $w\mapsto w(u)$ under $\rho$ is the centered normal law with variance $\|u\|_2^2$;
--   3. $w\mapsto w(u)$ is $\rho$-integrable, and
--   $$\int |w(u)|\,d\rho(w) = c\,\|u\|_2 .$$
--
--   In the language of the paper: $Z(u):=\sum_{n\ge1}u_nZ_n$ is a centered normal random variable with standard deviation $\|u\|_2$, so $\mathbf E|Z(u)|=c\|u\|_2$. This is the probabilistic input of the Gaussian Crofton embedding used to prove Theorem 3.16.
--
--   **Formalization Note.** The index is shifted to start at $0$. $\limsup$ is computed in $\mathbb R$; clause 1 shows that its junk value on divergent sequences occurs only on a $\rho$-null set. The normal law of variance $\sigma^2$ is Mathlib's `gaussianReal 0 σ²`; for $u=0$ it is the Dirac mass at $0$.
-- source:
--   Lyons, Distance covariance in metric spaces, arXiv:1106.5758 (version of 19 Dec. 2020), p. 18, proof of Theorem 3.16, second paragraph, and 'the series w(u) converges ρ-a.s.' (p. 18, after the second display)

import Mathlib
import Definitions.Def_DistCov_Hilbert_Setting

namespace DistCov.Hilbert

open MeasureTheory ProbabilityTheory

theorem gaussian_series (u : DistCov.Indep.L2N) :
    (∀ᵐ w ∂rho, Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, u n * w n) Filter.atTop
        (nhds (wEval w u))) ∧
    rho.map (fun w => wEval w u) = gaussianReal 0 (‖u‖₊ ^ 2) ∧
    Integrable (fun w => wEval w u) rho ∧
    ∫ w, |wEval w u| ∂rho = cGauss * ‖u‖ := by sorry

end DistCov.Hilbert
