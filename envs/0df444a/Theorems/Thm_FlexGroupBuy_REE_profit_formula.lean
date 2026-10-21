-- Prove2me | Theorems.Thm_FlexGroupBuy_REE_profit_formula
-- name    : FlexGroupBuy.REE.profit_formula
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:43.905473+00:00
-- url     : https://prove2.me/theorems/f655bd2c-ea14-4c3d-adaa-e6b22d631cdf
-- title:
--   Proof of Proposition 2, Online Appendix p. 4 — πG(x̄G) = (pG·γλN + L(1 − γ)λ(N − x̄G))/(N − (1 − γ)x̄G)
-- statement:
--   Under the standing assumptions and $N\ge1$, for every tipping state $\bar x^G\in[0,N]$ the long-run average profit, defined as revenue per expected renewal cycle, equals
--   $$
--   \pi^G(\bar x^G)=\frac{p^G(\bar x^G)\,\gamma\lambda N+L(1-\gamma)\lambda\,(N-\bar x^G)}{N-(1-\gamma)\bar x^G}.
--   $$
--
--   This closed form is the expression the firm maximizes in the proof of Proposition 2; its denominator is at least $\gamma N>0$ on $[0,N]$.
--
--   **Formalization Note.** $\pi^G$ is defined by the second line of the display on Online Appendix p. 4 (expected phase lengths $(N-\bar x^G)/(\gamma\lambda)$ and $\bar x^G/\lambda$), so this identity is the step to the third line.
-- source:
--   Hu, Liu & Zhai, Intertemporal Segmentation via Flexible-Duration Group Buying, SSRN 3242687 (version of 2019-12-06; MSOM forthcoming), Online Appendix p. 4, proof of Proposition 2

import Mathlib
import Definitions.Def_FlexGroupBuy_REE_Model

namespace FlexGroupBuy.REE

/-- Proof of Proposition 2 (Online Appendix p. 4): on `[0, N]` the long-run average profit equals
`(pG(x)·γλN + L(1 − γ)λ(N − x)) / (N − (1 − γ)x)`. -/
theorem profit_formula (P : Params) (hP : P.Standing) (N : ℕ) (hN : 1 ≤ N) :
    ∀ x ∈ Set.Icc (0 : ℝ) N,
      piG P N x = (pG P N x * P.gam * P.lam * N + P.L * (1 - P.gam) * P.lam * (N - x))
        / (N - (1 - P.gam) * x) := by sorry

end FlexGroupBuy.REE
