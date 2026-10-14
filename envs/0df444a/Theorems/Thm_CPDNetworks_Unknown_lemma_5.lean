-- Prove2me | Theorems.Thm_CPDNetworks_Unknown_lemma_5
-- name    : CPDNetworks.Unknown.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:13:10.624441+00:00
-- url     : https://prove2.me/theorems/f3a795c3-decb-4c0b-8c60-f4bd81559bad
-- title:
--   Lemma 5, p. 31 — for any α ∈ (0, 1) the type I error of the dyadic-grid test (14)–(15) is at most α
-- statement:
--   Fix $\epsilon\in(0,1/2]$ and let $C_\epsilon$ be a constant for which the noise bound of Lemma 12 holds. Let $n\ge1$, $T\ge2$, $\omega_n\ge0$ and $\alpha\in(0,1)$, and let $\psi_{n,T}$ be the test (14) that rejects when $\max_{t\in\mathcal T}\|Z_T(t)\|_{2\to2}$ exceeds
--   $$H_{\alpha,n,T}=2\sqrt2(1+\epsilon)\sqrt{\omega_n}+C_\epsilon\log\frac{4n\log_2(T)}{\alpha}.$$
--   Then its type I error over the null class $\mathcal S_n(\omega_n)$ is at most $\alpha$:
--   $$\alpha(\psi_{n,T})=\sup_{(\Theta^0,\Pi)\in\mathcal S_n(\omega_n)}\mathrm P_{(\Theta^0,\Pi)}\{\psi_{n,T}=1\}\le\alpha.$$
--
--   The extra factor $2\log_2T$ inside the logarithm pays for the union bound over the grid.
--
--   **Formalization Note.** "$C_\epsilon$ is a constant of Lemma 12" is a hypothesis here (the predicate of the Setting file); Lemma 12 shows such constants exist. The page says "less than $\alpha$" while its proof ends with "$\le\alpha$"; the Lean states $\le\alpha$. $n\ge1$, $T\ge2$ (so that $\mathcal D_T$ and the grid are nonempty and $\log_2T\ge1$) and $\omega_n\ge0$ are the paper's implicit standing assumptions.
-- source:
--   Enikeeva and Klopp, Change-point detection in dynamic networks with missing links, arXiv:2106.14470v2, p. 31, Lemma 5 (with (14)–(15), p. 12)

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Unknown_Setting

open scoped Matrix
open HighDimProb.RandomMatrices

namespace CPDNetworks.Unknown

/-- Lemma 5, p. 31: the type I error of the dyadic-grid test (14)–(15) is at most `α`. -/
theorem lemma_5 (ε Cε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hC : CPDNetworks.Known.IsNoiseConst ε Cε)
    (n T : ℕ) (ω α : ℝ) (hn : 1 ≤ n) (hT : 2 ≤ T) (hω : 0 ≤ ω)
    (hα : 0 < α) (hα1 : α < 1) :
    CPDNetworks.Lower.typeI (n := n) (T := T) ω (testGrid (thrGrid ε Cε ω α n T)) ≤ α := by sorry

end CPDNetworks.Unknown
