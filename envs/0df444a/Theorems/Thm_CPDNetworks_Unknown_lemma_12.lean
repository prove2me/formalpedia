-- Prove2me | Theorems.Thm_CPDNetworks_Unknown_lemma_12
-- name    : CPDNetworks.Unknown.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:54.465229+00:00
-- url     : https://prove2.me/theorems/6d690a5f-6f9f-4f14-92aa-61dea91860f4
-- title:
--   Lemma 12, p. 51 — for every ϵ ∈ (0, 1/2] an absolute C_ϵ makes the CUSUM noise bound (38) hold with probability > 1 − δ
-- statement:
--   For every $\epsilon\in(0,1/2]$ there is an absolute constant $C_\epsilon>0$ with the following property. Let $n,T\ge1$, $1\le t\le T-1$, let $B^1,\dots,B^T\in\mathcal C^0_n$ (symmetric, entries in $[0,1]$, zero diagonal), and let $Y^s_{ij}\sim\mathrm{Bernoulli}(B^s_{ij})$ be independent over $i<j$ and $s$, so that $X^s=Y^s-B^s$ has independent centred entries taking values in $\{1-B^s_{ij},-B^s_{ij}\}$. Let $\xi(t)=\sqrt{t(T-t)/T}\,\big(\frac1t\sum_{s\le t}X^s-\frac1{T-t}\sum_{s>t}X^s\big)$. Then for every $\delta\in(0,1)$, with probability larger than $1-\delta$,
--   $$\|\xi(t)\|_{2\to2}\le2\sqrt2(1+\epsilon)\sqrt{\frac{t(T-t)}{T}}\Big[\frac1{t^2}\sum_{s=1}^t\|B^s\|_{1,\infty}+\frac1{(T-t)^2}\sum_{s=t+1}^T\|B^s\|_{1,\infty}\Big]^{1/2}+C_\epsilon\log\frac{2n}{\delta}.\qquad(38)$$
--
--   This controls the noise of the Matrix CUSUM at a fixed time; the level and the power of the dyadic-grid test (Lemmas 5 and 6) both follow from it.
--
--   **Formalization Note.** $C_\epsilon$ is chosen before $n$, $T$, $t$, $B$ and $\delta$, as "absolute constant" requires. The paper states the setting for independent entries "for any $1\le i,j\le n$"; for the symmetric matrices of the model this means the entries with $i<j$, and the Lean takes $B^s\in\mathcal C^0_n$, which is the case the paper applies the lemma to ($B^s=\Pi\odot\Theta^s$). The probability is the finite product law of the Setting file; "larger than $1-\delta$" is strict.
-- source:
--   Enikeeva and Klopp, Change-point detection in dynamic networks with missing links, arXiv:2106.14470v2, pp. 50–51, setting before Lemma 12 and Lemma 12, display (38)

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Unknown_Setting

open scoped Matrix
open HighDimProb.RandomMatrices

namespace CPDNetworks.Unknown

/-- Lemma 12, p. 51: for every `ϵ ∈ (0, 1/2]` there is an absolute constant `C_ϵ` for which the
CPDNetworks.Known.noise bound (38) holds with probability larger than `1 − δ`, for every `δ ∈ (0, 1)`. -/
theorem lemma_12 : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ C : ℝ, 0 < C ∧ CPDNetworks.Known.IsNoiseConst ε C := by sorry

end CPDNetworks.Unknown
