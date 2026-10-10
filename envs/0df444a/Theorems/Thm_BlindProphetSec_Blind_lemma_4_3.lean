-- Prove2me | Theorems.Thm_BlindProphetSec_Blind_lemma_4_3
-- name    : BlindProphetSec.Blind.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:38:45.457199+00:00
-- url     : https://prove2.me/theorems/6d0ca66d-ca71-4cec-bfee-aa2447b21c59
-- title:
--   Lemma 4.3, p. 14 — for piecewise-constant α = α_{α₁…α_m} with α_m > 0, E(V_{σ_T}) ≥ min_{j∈[m+1]} f_j(α₁,…,α_m) · E(maxᵢ Vᵢ)
-- statement:
--   Let $m\ge1$ and $1>\alpha_1\ge\alpha_2\ge\dots\ge\alpha_m>0$, and let $\alpha=\alpha_{\alpha_1,\dots,\alpha_m}$ be the piecewise-constant function $\alpha(x)=\sum_{j\in[m]}\alpha_j\mathbf 1_{[\frac{j-1}m,\frac jm)}(x)$. Let $F_1,\dots,F_n$ be continuous laws of independent nonnegative random variables arriving in uniformly random order and let $T$ be the stopping time of the blind strategy $\alpha$. Then
--   $$\mathbb E(V_{\sigma_T})\;\ge\;\min_{j\in[m+1]}f_j(\alpha_1,\dots,\alpha_m)\cdot\mathbb E\big(\max_{i\in[n]}V_i\big),$$
--   where $f_j$ is given by
--   $$f_j=\begin{cases}\sum_{k=1}^m\big(\prod_{l\in[k-1]}\alpha_l\big)^{1/m}\dfrac{1-\alpha_k^{1/m}}{-\ln\alpha_k} & j=1,\\[2mm] \sum_{k\in[j-1]}\dfrac{1-\alpha_k}{m(1-\alpha_j)}+\sum_{k=j}^m\big(\prod_{l\in[k-1]}\alpha_l\big)^{1/m}g_{m,\alpha_1}(k-1)\dfrac{1-\alpha_k^{1/m}}{-\ln\alpha_k} & j\in\{2,\dots,m\},\\[2mm] \dfrac1m\sum_{k\in[m]}(1-\alpha_k) & j=m+1,\end{cases}$$
--   and $g_{m,p}(k)=1/(1-\frac km(1-p))$ for $k\le m/2$, $g_{m,p}(k)=2/(1+p)$ for $k>m/2$.
--
--   The bound depends only on $(\alpha_1,\dots,\alpha_m)$, never on the instance, so optimizing it numerically over the $\alpha_j$ yields a guarantee for blind strategies.
--
--   **Formalization Note.** The paper writes the ratio $\mathbb E(V_{\sigma_T})/\mathbb E(\max_iV_i)$; the statement is the multiplied-out form in $[0,\infty]$, which avoids $0/0$ and $\infty/\infty$. The paper prints only $\alpha_m>0$. The hypothesis $\alpha_1<1$ is added: at $\alpha_k=1$ the factor $(1-\alpha_k^{1/m})/(-\ln\alpha_k)$ is $0/0$ on the page, and at $\alpha_j=1$ the term $(1-\alpha_k)/(m(1-\alpha_j))$ divides by zero; Lean would return junk values there. With $\alpha_1<1$ every $\alpha_k\in(0,1)$ and every term is the paper's. The coefficients are a 1-based sequence `a : ℕ → ℝ`, nonincreasing on $\{1,\dots,m\}$.
-- source:
--   Correa, Saona & Ziliotto, Prophet Secretary Through Blind Strategies, arXiv:1807.07483v2, p. 14, Lemma 4.3 (with g_{m,p} and α_{α1,…,αm} from p. 13); proof pp. 14–16

import Mathlib
import Definitions.Def_BlindProphetSec_Blind_Setting

namespace BlindProphetSec.Blind

open MeasureTheory

theorem lemma_4_3 (m : ℕ) (hm : 1 ≤ m) (a : ℕ → ℝ) (ha_anti : AntitoneOn a (Set.Icc 1 m))
    (ham : 0 < a m) (ha1 : a 1 < 1)
    {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (hnn : ∀ i, μ i (Set.Iio 0) = 0) :
    ENNReal.ofReal ((Finset.Icc 1 (m + 1)).inf' ⟨1, by simp⟩ (fFun m a)) * Emax μ ≤
      blindValue (pieceAlpha m a) μ := by sorry

end BlindProphetSec.Blind
