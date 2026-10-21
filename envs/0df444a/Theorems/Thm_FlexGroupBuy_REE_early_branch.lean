-- Prove2me | Theorems.Thm_FlexGroupBuy_REE_early_branch
-- name    : FlexGroupBuy.REE.early_branch
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:59.983618+00:00
-- url     : https://prove2.me/theorems/a88e0483-ddb9-4153-8834-4efb0edd253d
-- title:
--   Proof of Proposition 2, Online Appendix p. 4 — early branch x̄G ⩽ x̄G1: closed-form profit with positive derivative
-- statement:
--   Under the standing assumptions and $N\ge1$:
--
--   1. For every $\bar x^G\in[0,N]$ with $\bar x^G\le\bar x^G_1$,
--   $$
--   \pi^G(\bar x^G)=\frac{[(\theta-1)H+L]\gamma\lambda N+L(1-\gamma)\lambda(N-\bar x^G)-cN(N-1)+c(1-\gamma)N\bar x^G}{N-(1-\gamma)\bar x^G}.
--   $$
--   2. The right-hand side, as a function of $\bar x^G$, is differentiable wherever $(1-\gamma)\bar x^G<N$, with derivative
--   $$
--   \frac{(1-\gamma)N\,[c+(\theta-1)H\gamma\lambda]}{[N-(1-\gamma)\bar x^G]^2}.
--   $$
--   3. This derivative is strictly positive at every such point.
--
--   Hence on the early branch the profit strictly increases up to $\bar x^G_1$.
--
--   **Formalization Note.** The paper states the branch for $1\le\bar x^G\le\bar x^G_1$; part 1 is stated on the wider range $0\le\bar x^G\le\bar x^G_1$, which holds because $p^G(0)=\bar p^G_2(0)$ and the relaxed tipping state is real.
-- source:
--   Hu, Liu & Zhai, Intertemporal Segmentation via Flexible-Duration Group Buying, SSRN 3242687 (version of 2019-12-06; MSOM forthcoming), Online Appendix p. 4, proof of Proposition 2

import Mathlib
import Definitions.Def_FlexGroupBuy_REE_Model

namespace FlexGroupBuy.REE

/-- Proof of Proposition 2 (Online Appendix p. 4), early branch `x ≤ x̄G1`: (a) the profit equals
the printed fraction (on all of `[0, x̄G1] ∩ [0, N]`, i.e. including `x ∈ [0, 1)`); (b) the fraction
has the printed derivative wherever its denominator is positive; (c) that derivative is positive. -/
theorem early_branch (P : Params) (hP : P.Standing) (N : ℕ) (hN : 1 ≤ N) :
    (∀ x ∈ Set.Icc (0 : ℝ) N, x ≤ xbar1 P N →
      piG P N x = (((P.theta - 1) * P.H + P.L) * P.gam * P.lam * N
          + P.L * (1 - P.gam) * P.lam * (N - x) - P.c * N * ((N : ℝ) - 1)
          + P.c * (1 - P.gam) * N * x) / (N - (1 - P.gam) * x)) ∧
    (∀ x : ℝ, (1 - P.gam) * x < N →
      HasDerivAt
        (fun y : ℝ => (((P.theta - 1) * P.H + P.L) * P.gam * P.lam * N
          + P.L * (1 - P.gam) * P.lam * (N - y) - P.c * N * ((N : ℝ) - 1)
          + P.c * (1 - P.gam) * N * y) / (N - (1 - P.gam) * y))
        ((1 - P.gam) * N * (P.c + (P.theta - 1) * P.H * P.gam * P.lam)
          / (N - (1 - P.gam) * x) ^ 2) x) ∧
    (∀ x : ℝ, (1 - P.gam) * x < N →
      0 < (1 - P.gam) * N * (P.c + (P.theta - 1) * P.H * P.gam * P.lam)
          / (N - (1 - P.gam) * x) ^ 2) := by sorry

end FlexGroupBuy.REE
