-- Prove2me | Theorems.Thm_CertDRO_NNSmooth_proposition_5_part_1
-- name    : CertDRO.NNSmooth.proposition_5_part_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:33:20.581011+00:00
-- url     : https://prove2.me/theorems/65ad764f-9742-41bd-8071-62a60f5eeef7
-- title:
--   Proposition 5 (first part) — F_l(θ; ·) is α_l(θ)-Lipschitz
-- statement:
--   Let a network of depth $L$ satisfy Assumption E with layer constants $L^0_l, L^1_l$, and let $\alpha_l(\theta)=\prod_{j=1}^{l}L^0_j\|\theta_j\|_{\mathrm{op}}$ as in (21). Then for every $l=0,\dots,L$ and all inputs $x,x'$,
--   $$\big\|F_l(\theta;x)-F_l(\theta;x')\big\|_2\le\alpha_l(\theta)\,\|x-x'\|_2 .$$
--
--   This is the Lipschitz half of Proposition 5: the input-Lipschitz constant of a deep network is at most the product of the layer Lipschitz constants and spectral norms. It is used to bound terms (b) and (c) in the proof of the second half.
--
--   **Formalization Note** The case $l=0$ ($F_0(\theta;x)=x$, $\alpha_0=1$) is included and trivial. All norms are Euclidean and $\|\theta_j\|_{\mathrm{op}}$ is the operator norm of the weight as a continuous linear map.
-- source:
--   Sinha, Namkoong, Volpi, Duchi, Certifying Some Distributional Robustness with Principled Adversarial Training, arXiv:1710.10571v5, p. 13, Proposition 5 (first part); proof pp. 44–45, §B.8

import Mathlib
import Definitions.Def_CertDRO_NNSmooth_Network

namespace CertDRO.NNSmooth

open Network

/-- Proposition 5, first part (p. 13; proof pp. 44–45). Under Assumption E for the first `L`
layers, every `F_l(θ; ·)`, `l ≤ L`, is `α_l(θ)`-Lipschitz for the ℓ²-norm, with `α_l(θ)` given
by (21). -/
theorem proposition_5_part_1 (N : Network) (L : ℕ) (L0 L1 : ℕ → ℝ)
    (hE : N.AssumptionE L L0 L1) :
    ∀ l ≤ L, ∀ x x' : E (N.dO 0), ‖N.F l x - N.F l x'‖ ≤ N.α L0 l * ‖x - x'‖ := by sorry

end CertDRO.NNSmooth
