-- Prove2me | Theorems.Thm_FlexGroupBuy_REE_proposition_2
-- name    : FlexGroupBuy.REE.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:45.872006+00:00
-- url     : https://prove2.me/theorems/21acbba6-9733-46ad-9e0e-3c4e8caeab90
-- title:
--   Proposition 2, p. 14 — optimal tipping state: N if N ⩽ N̄1, 0 if N ⩽ N̄2, and x̄G1 ∈ (0, N) (intertemporal segmentation) above, with closed-form pG, πG
-- statement:
--   Assume $H>L>0$, $0<\gamma<1$, $\lambda>0$, $c>0$, $\theta>1$ and an integer batch size $N\ge1$. Let $\pi^G$ be the firm's long-run average profit as a function of the tipping state $\bar x^G\in[0,N]$, with regular price $r^G=L$ and group-buying price $p^G$ (see the model definition), and let
--   $$
--   \bar N_1=\frac{(\theta-1)(1-\gamma)L\lambda}{c}+1-\gamma,\qquad \bar N_2=\frac{(\theta-1)(H-L)\gamma\lambda}{c}+1-\gamma,\qquad \bar x^G_1=N-1+\gamma-\frac{(\theta-1)(H-L)\gamma\lambda}{c}.
--   $$
--   Then:
--
--   1. **(i) $H/L\le 1/\gamma$.**
--      - (i-1) If $N\le\bar N_1$, then $\bar x^G=N$ (scenario $\{H+L\}$) maximizes $\pi^G$ over $[0,N]$, with $p^G=\theta L-c(N-1)/\lambda$ and $\pi^G=\theta L\lambda-c(N-1)$.
--      - (i-2) If $N>\bar N_1$, then $0<\bar x^G_1<N$ (scenario $\{H;H+L\}$) and $\bar x^G_1$ maximizes $\pi^G$ over $[0,N]$, with $p^G=\theta L+\gamma(\theta-1)(H-L)-c(N-2+\gamma)/\lambda$ and $\pi^G=\pi^G_1$.
--   2. **(ii) $H/L>1/\gamma$.**
--      - (ii-1) If $N\le\bar N_2$, then $\bar x^G=0$ (scenario $\{H\}$) maximizes $\pi^G$ over $[0,N]$, with $p^G=(\theta-1)H+L-c(N-1)/(\gamma\lambda)$ and $\pi^G=(\theta-1)H\gamma\lambda+L\lambda-c(N-1)$.
--      - (ii-2) If $N>\bar N_2$, then $0<\bar x^G_1<N$ and $\bar x^G_1$ maximizes $\pi^G$ over $[0,N]$, with the same $p^G$ and $\pi^G=\pi^G_1$ as in (i-2).
--
--   Here
--   $$
--   \pi^G_1=\frac{(\theta-1)(H-L)L(1-\gamma)\gamma\lambda^2+(\theta-1)cHN\gamma^2\lambda+cL\lambda[1+\theta(1-\gamma)\gamma N+\gamma^2(N+1)-2\gamma]-c^2\gamma N(N-2+\gamma)}{c[1+\gamma(N-2+\gamma)]+(\theta-1)(H-L)(1-\gamma)\gamma\lambda}.
--   $$
--
--   The proposition says when a uniform-price group-buying campaign admits only high-end customers, both segments from the start, or high-end customers first and both segments later (**intertemporal segmentation**). The last happens for every batch size above an explicit threshold.
--
--   **Formalization Note.** "$\{S\}$ is an REE" is read, as in the proof, as "the firm's optimal tipping state is the one of scenario $S$": $\bar x^G=0$, $0<\bar x^G<N$, $\bar x^G=N$ for $\{H\}$, $\{H;H+L\}$, $\{H+L\}$ (p. 13). The tipping state is the paper's real relaxation $\bar x^G\in[0,N]$ (footnote 1, Online Appendix p. 2), and optimality is over all of $[0,N]$, not uniqueness. The optimization is the paper's reduced problem: $r^G=L$, ICH and ICL2 binding, and IRH, IRL2, ICL1 left unchecked as in the proof.
-- source:
--   Hu, Liu & Zhai, Intertemporal Segmentation via Flexible-Duration Group Buying, SSRN 3242687 (version of 2019-12-06; MSOM forthcoming), p. 14, Proposition 2; proof Online Appendix pp. 3–5

import Mathlib
import Definitions.Def_FlexGroupBuy_REE_Model

namespace FlexGroupBuy.REE

/-- Proposition 2 (p. 14) with the closed forms its proof states (Online Appendix pp. 4–5): the
optimal tipping state over `[0, N]` is `N` ({H + L}), `x̄G1 ∈ (0, N)` ({H;H + L}) or `0` ({H}),
according to `H/L` versus `1/γ` and `N` versus `N̄1`, `N̄2`, with the printed price and profit. -/
theorem proposition_2 (P : Params) (hP : P.Standing) (N : ℕ) (hN : 1 ≤ N) :
    (P.H / P.L ≤ 1 / P.gam →
      ((N : ℝ) ≤ Nbar1 P →
          IsOptimalTip P N N ∧
          pG P N N = P.theta * P.L - P.c * ((N : ℝ) - 1) / P.lam ∧
          piG P N N = P.theta * P.L * P.lam - P.c * ((N : ℝ) - 1)) ∧
      (Nbar1 P < N →
          0 < xbar1 P N ∧ xbar1 P N < N ∧ IsOptimalTip P N (xbar1 P N) ∧
          pG P N (xbar1 P N) = P.theta * P.L + P.gam * (P.theta - 1) * (P.H - P.L)
                                 - P.c * ((N : ℝ) - 2 + P.gam) / P.lam ∧
          piG P N (xbar1 P N) = piG1 P N)) ∧
    (1 / P.gam < P.H / P.L →
      ((N : ℝ) ≤ Nbar2 P →
          IsOptimalTip P N 0 ∧
          pG P N 0 = (P.theta - 1) * P.H + P.L - P.c * ((N : ℝ) - 1) / (P.gam * P.lam) ∧
          piG P N 0 = (P.theta - 1) * P.H * P.gam * P.lam + P.L * P.lam - P.c * ((N : ℝ) - 1)) ∧
      (Nbar2 P < N →
          0 < xbar1 P N ∧ xbar1 P N < N ∧ IsOptimalTip P N (xbar1 P N) ∧
          pG P N (xbar1 P N) = P.theta * P.L + P.gam * (P.theta - 1) * (P.H - P.L)
                                 - P.c * ((N : ℝ) - 2 + P.gam) / P.lam ∧
          piG P N (xbar1 P N) = piG1 P N)) := by sorry

end FlexGroupBuy.REE
