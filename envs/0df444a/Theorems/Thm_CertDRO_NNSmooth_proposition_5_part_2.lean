-- Prove2me | Theorems.Thm_CertDRO_NNSmooth_proposition_5_part_2
-- name    : CertDRO.NNSmooth.proposition_5_part_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:33:08.392793+00:00
-- url     : https://prove2.me/theorems/62dc8a16-7349-415a-ae8a-a2c680937f52
-- title:
--   Proposition 5 (second part) — J_xF_l(θ; ·) is β_l(θ)-Lipschitz in operator norm
-- statement:
--   Let a network of depth $L$ satisfy Assumption E with layer constants $L^0_l, L^1_l$, and let
--   $$\alpha_l(\theta)=\prod_{j=1}^{l}L^0_j\|\theta_j\|_{\mathrm{op}},\qquad\beta_l(\theta)=\alpha_l(\theta)\sum_{j=1}^{l}\frac{L^1_j}{(L^0_j)^2}\,\alpha_j(\theta)$$
--   as in (21). Then for every $l=0,\dots,L$ and all inputs $x,x'$,
--   $$\big\|J_xF_l(\theta;x)-J_xF_l(\theta;x')\big\|_{\mathrm{op}}\le\beta_l(\theta)\,\|x-x'\|_2 ,$$
--   where $\|\cdot\|_{\mathrm{op}}$ is the $\ell_2$-operator (spectral) norm.
--
--   This is the smoothness half of Proposition 5: it bounds the input-smoothness constant of a deep network, the quantity $L_{zz}$ that the paper's certificates require to be smaller than the penalty $\gamma$.
--
--   **Formalization Note** The Jacobian is the Fréchet derivative `fderiv ℝ (F l)`, a continuous linear map, with the operator norm. The case $l=0$ (identity map, $\beta_0=0$) is included and trivial. The positivity $L^0_l>0$ of Assumption E makes the quotients in (21) well defined.
-- source:
--   Sinha, Namkoong, Volpi, Duchi, Certifying Some Distributional Robustness with Principled Adversarial Training, arXiv:1710.10571v5, p. 13, Proposition 5 (second part); proof pp. 45–46, §B.8

import Mathlib
import Definitions.Def_CertDRO_NNSmooth_Network

namespace CertDRO.NNSmooth

open Network

/-- Proposition 5, second part (p. 13; proof pp. 45–46). Under Assumption E for the first `L`
layers, the Jacobian `x ↦ J_x F_l(θ; x)` of every `F_l(θ; ·)`, `l ≤ L`, is `β_l(θ)`-Lipschitz
from the ℓ²-norm on inputs to the ℓ²-operator norm on Jacobians, with `β_l(θ)` given by (21). -/
theorem proposition_5_part_2 (N : Network) (L : ℕ) (L0 L1 : ℕ → ℝ)
    (hE : N.AssumptionE L L0 L1) :
    ∀ l ≤ L, ∀ x x' : E (N.dO 0),
      ‖fderiv ℝ (N.F l) x - fderiv ℝ (N.F l) x'‖ ≤ N.β L0 L1 l * ‖x - x'‖ := by sorry

end CertDRO.NNSmooth
