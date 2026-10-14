-- Prove2me | Theorems.Thm_CPDNetworks_Known_lemma_12
-- name    : CPDNetworks.Known.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:26.905096+00:00
-- url     : https://prove2.me/theorems/b74336d8-b27f-414a-b3ed-9e18ac864828
-- title:
--   Lemma 12 — $\|\xi(t)\|_{2\to2}\le2\sqrt2(1+\epsilon)\sqrt{t(T-t)/T}[\dots]^{1/2}+C_\epsilon\log(2n/\delta)$ w.p. $>1-\delta$
-- statement:
--   For every $\epsilon\in(0,1/2]$ there is an absolute constant $C_\epsilon>0$ such that the following holds for all $n,T\ge1$, all $1\le t\le T-1$, all symmetric zero-diagonal matrices $B^1,\dots,B^T$ with entries in $[0,1]$, and all $\delta\in(0,1)$. Let $X^s=Y^s-B^s$, where the entries $Y^s_{ij}$, $i<j$, are independent Bernoulli$(B^s_{ij})$ variables, independent over $s$, and let
--   $$\xi(t)=\sqrt{\tfrac{t(T-t)}{T}}\Big(\tfrac1t\sum_{s=1}^tX^s-\tfrac1{T-t}\sum_{s=t+1}^TX^s\Big).$$
--   Then, with probability larger than $1-\delta$,
--   $$\|\xi(t)\|_{2\to2}\le2\sqrt2(1+\epsilon)\sqrt{\tfrac{t(T-t)}{T}}\Big[\tfrac1{t^2}\sum_{s=1}^t\|B^s\|_{1,\infty}+\tfrac1{(T-t)^2}\sum_{s=t+1}^T\|B^s\|_{1,\infty}\Big]^{1/2}+C_\epsilon\log\frac{2n}{\delta}.$$
--
--   This controls the noise of the Matrix CUSUM uniformly in the network size, the horizon, the time point and the edge probabilities, and it is what fixes the threshold of the test.
--
--   **Formalization Note.** The page takes $X^t\in[-1,1]^{n\times n}$ with independent centred Bernoulli entries for all $1\le i,j\le n$; here the matrices are the symmetric zero-diagonal centred observations of the network model, the only reading compatible with Proposition 11 and the one used in the application. The constant $C_\epsilon$ is chosen before every other quantity.
-- source:
--   Enikeeva and Klopp, Change-point detection in dynamic networks with missing links, arXiv:2106.14470v2, pp. 50–51, Lemma 12, display (38)

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Known_Setting
open scoped Matrix
open HighDimProb.RandomMatrices

namespace CPDNetworks.Known

/-- Lemma 12, p. 51: for every `ϵ ∈ (0, 1/2]` there is an absolute constant `C_ϵ > 0` such that
display (38) holds with probability larger than `1 − δ`, uniformly in `n, T, t, B, δ`. -/
theorem lemma_12 : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ C : ℝ, 0 < C ∧ IsNoiseConst ε C := by sorry

end CPDNetworks.Known
