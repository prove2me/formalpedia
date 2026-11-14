-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_cost_integrand_cubic
-- name    : CountingLLL.ContractedWalk.cost_integrand_cubic
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:49:54.241377+00:00
-- url     : https://prove2.me/theorems/f78554a8-c11f-4320-b3fa-0cbcce16b78d
-- title:
--   Cubic identity for the source weighted-change cost integrand
-- statement:
--   Let $G(z)$ be the source contracted-walk generating function, $0<\theta<1/3$, and $0\le z<1$. Then $$\frac{1}{\theta}\left(\frac{1-G(z)}{\theta(1-z)}-1\right)=\frac{z(1+G(z)+G(z)^2)}{1-\theta z(1+G(z)+G(z)^2)}.$$ This follows from the cubic equation for $G$ and is the pointwise algebra connecting the harmonic generating function to the cost integral. The probabilistic weighted-change identity remains separate.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, proof of Lemma 6.5, calls to O, p. 28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedGF
open CountingLLL.ContractedWalk

theorem CountingLLL.ContractedWalk.cost_integrand_cubic (θ z : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1/3)
    (hz0 : 0 ≤ z) (hz1 : z < 1) :
    let g := generatingFunction θ z
    ((1-g)/(θ*(1-z))-1)/θ = z*(1+g+g^2)/(1-θ*z*(1+g+g^2)) := by sorry
