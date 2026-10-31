-- Prove2me | Theorems.Thm_CtrlVolMFG_lemma_3_10
-- name    : CtrlVolMFG.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:24:57.646756+00:00
-- url     : https://prove2.me/theorems/adeacf36-d5db-4a70-b7a0-1aa5ec8a2d6d
-- title:
--   Lemma 3.10 — the structural condition (2.19) projected onto empirical measures
-- statement:
--   Let Assumption 2.19 hold, with constant $C_H$ in (2.19). Then for all $\mathbf x,\bar{\mathbf x},\mathbf y,\bar{\mathbf y}\in(\mathbb R^n)^N$ and $\mathbf z,\bar{\mathbf z},\mathbf z^0,\bar{\mathbf z}^0\in(\mathbb R^{n\times d})^N$,
--   $$\sum_{i=1}^N\Big(-\big(D_xH(x^i,y^i,z^i,z^{0,i},m^N_{\mathbf x})-D_xH(\bar x^i,\bar y^i,\bar z^i,\bar z^{0,i},m^N_{\bar{\mathbf x}})\big)\cdot(x^i-\bar x^i)+\big(D_yH(\dots)-D_yH(\dots)\big)\cdot(y^i-\bar y^i)+\big(D_zH(\dots)-D_zH(\dots)\big)\cdot(z^i-\bar z^i)+\big(D_{z^0}H(\dots)-D_{z^0}H(\dots)\big)\cdot(z^{0,i}-\bar z^{0,i})\Big)\le-C_H\sum_{i=1}^N|x^i-\bar x^i|^2.$$
--
--   This is the finite-dimensional form of the monotonicity used in the Itô computation of Proposition 3.16.
--
--   Differences from the source:
--   - encoding: "for any square-integrable random variables" in (1.6), (2.16), (2.19) → for every coupling $\pi$ with finite second moments, the laws being the marginals of $\pi$, whenever the integrand is integrable; reason: random variables enter only through their joint law, and every coupling is a joint law on an atomless space
--   - encoding: "$C_H$" of Assumption 2.19 → any $C_H$ for which (2.19) holds (`DisplMonoH D CH`), with Assumption 2.19 assumed; reason: the constant of the assumption is such a $C_H$
--   - encoding: $\mathbb R^{n\times d}$ with the Frobenius norm and $A\cdot B=\mathrm{tr}(A^\top B)$ → `EuclideanSpace ℝ (Fin n × Fin d)`; reason: same norm and inner product
--   - encoding: $N\in\mathbb N$ → any $N\ge0$; reason: for $N=0$ both sides are $0$
--   - encoding: players $i\in\{1,\dots,N\}$ → players `i : Fin N`, player $i$ of the paper is index $i-1$; reason: relabelling
-- source:
--   Jackson & Tangpi, Quantitative Convergence for Displacement Monotone Mean Field Games with Controlled Volatility, arXiv:2304.04543v2, Lemma 3.10, pp.22–23; (2.19) p.16

import Mathlib
import Definitions.Def_CtrlVolMFG_IsSol_3_6

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace CtrlVolMFG

/-- Lemma 3.10 (Jackson & Tangpi, arXiv:2304.04543v2, pp.22–23): let Assumption 2.19 hold, with
constant `C_H` in (2.19). Then for any `x, x̄, y, ȳ ∈ (ℝⁿ)ᴺ` and `z, z̄, z⁰, z̄⁰ ∈ (ℝ^{n×d})ᴺ`,
`∑ᵢ [ −(D_xH(xⁱ, yⁱ, zⁱ, z^{0,i}, m^N_x) − D_xH(x̄ⁱ, ȳⁱ, z̄ⁱ, z̄^{0,i}, m^N_x̄))·(xⁱ − x̄ⁱ)
 + (D_yH(…) − D_yH(…))·(yⁱ − ȳⁱ) + (D_zH(…) − D_zH(…))·(zⁱ − z̄ⁱ)
 + (D_{z⁰}H(…) − D_{z⁰}H(…))·(z^{0,i} − z̄^{0,i}) ] ≤ −C_H ∑ᵢ |xⁱ − x̄ⁱ|²`. -/
theorem lemma_3_10 {n k d : ℕ} (D : Data n k d) (h19 : Assumption_2_19 D) (CH : ℝ)
    (hCH : DisplMonoH D CH) (N : ℕ) (x x' y y' : Fin N → Rn n) (z z' z0 z0' : Fin N → Mat n d) :
    ∑ i, monoH D ((x i, y i, z i, z0 i), (x' i, y' i, z' i, z0' i)) (empP2 x) (empP2 x') ≤
      -CH * ∑ i, ‖x i - x' i‖ ^ 2 := by sorry

end CtrlVolMFG
