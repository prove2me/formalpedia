-- Prove2me | Theorems.Thm_FlexGroupBuy_REE_price_switch
-- name    : FlexGroupBuy.REE.price_switch
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:44.047799+00:00
-- url     : https://prove2.me/theorems/816733c7-64be-48d9-adfd-0b6066c55ace
-- title:
--   Proof of Proposition 2, Online Appendix p. 3 — p̄G1(x̄G) < p̄G2(x̄G) if and only if x̄G > x̄G1
-- statement:
--   Under the standing assumptions and $N\ge1$, for every tipping state $\bar x^G\in[0,N]$,
--   $$
--   \bar p^G_1(\bar x^G)<\bar p^G_2(\bar x^G)\iff \bar x^G>\bar x^G_1,\qquad \bar x^G_1=N-1+\gamma-\frac{(\theta-1)(H-L)\gamma\lambda}{c},
--   $$
--   where $\bar p^G_1(\bar x^G)=\theta L-c\,w^G(\bar x^G)$ is the price at which low-end customers are indifferent at the tipping state and $\bar p^G_2(\bar x^G)=(\theta-1)H+L-c\,w^G(N)$ the price at which high-end customers are indifferent at state $N$.
--
--   This identifies which incentive constraint binds: the uniform price $p^G=\min\{\bar p^G_1,\bar p^G_2\}$ equals $\bar p^G_2$ up to $\bar x^G_1$ and $\bar p^G_1$ beyond it.
--
--   **Formalization Note.** The equivalence is stated on all of $[0,N]$; at $\bar x^G=N$ both sides are true.
-- source:
--   Hu, Liu & Zhai, Intertemporal Segmentation via Flexible-Duration Group Buying, SSRN 3242687 (version of 2019-12-06; MSOM forthcoming), Online Appendix p. 3, proof of Proposition 2

import Mathlib
import Definitions.Def_FlexGroupBuy_REE_Model

namespace FlexGroupBuy.REE

/-- Proof of Proposition 2 (Online Appendix p. 3): on `[0, N]`, `p̄G1(x) < p̄G2(x)` if and only if
`x > x̄G1`. -/
theorem price_switch (P : Params) (hP : P.Standing) (N : ℕ) (hN : 1 ≤ N) :
    ∀ x ∈ Set.Icc (0 : ℝ) N, pbar1 P x < pbar2 P N x ↔ xbar1 P N < x := by sorry

end FlexGroupBuy.REE
