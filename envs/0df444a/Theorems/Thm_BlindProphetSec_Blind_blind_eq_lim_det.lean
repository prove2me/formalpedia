-- Prove2me | Theorems.Thm_BlindProphetSec_Blind_blind_eq_lim_det
-- name    : BlindProphetSec.Blind.blind_eq_lim_det
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:37:42.457036+00:00
-- url     : https://prove2.me/theorems/a9dd49a5-d30a-4b60-a852-edfe1783c6ca
-- title:
--   §3, p. 7, display after Definition 3.1 — the blind strategy is the limit of deterministic blind strategies on zero-padded instances
-- statement:
--   Let $\alpha:[0,1]\to[0,1]$ be nonincreasing and let $F_1,\dots,F_n$ be continuous laws of nonnegative independent random variables with $\mathbb E(\max_i V_i)<\infty$. For $m\ge0$ add to the instance $m$ random variables identically equal to $0$, $F_{n+i}=\mathbf 1_{[0,\infty)}$ for $i=1,\dots,m$, and let $T_m$ be the stopping time of the deterministic blind strategy $\alpha$ (Definition 3.1) on the padded instance $F_1,\dots,F_{n+m}$, with the $n+m$ values arriving in uniformly random order. Let $T$ be the stopping time of the blind strategy $\alpha$ on the original instance. Then
--   $$\lim_{m\to\infty}\mathbb E(V_{\sigma_{T_m}})=\mathbb E(V_{\sigma_T}).$$
--
--   This reduces the analysis of blind strategies, which use auxiliary randomization $u_1,\dots,u_n$, to deterministic blind strategies on large instances.
--
--   **Formalization Note.** The limit is taken in $[0,\infty]$. The hypothesis $\mathbb E(\max_i V_i)<\infty$ is not printed on the page; it is added because the paper's ratios take the prophet's value finite, and without it the display fails: for $n=1$, $V_1$ continuous with infinite mean, and $\alpha=1$ on $[0,1)$, $\alpha(1)=0$, the blind strategy never stops (value $0$) while every padded deterministic strategy stops at the last time with probability $1/(1+m)$ and has value $\infty$. Continuity is assumed for the original laws only, as on the page; the padding variables are point masses at $0$.
-- source:
--   Correa, Saona & Ziliotto, Prophet Secretary Through Blind Strategies, arXiv:1807.07483v2, p. 7, §3, display after Definition 3.1

import Mathlib
import Definitions.Def_BlindProphetSec_Blind_Setting

namespace BlindProphetSec.Blind

open MeasureTheory Filter Topology

theorem blind_eq_lim_det (α : ℝ → ℝ) (hα_anti : AntitoneOn α (Set.Icc 0 1))
    (hα_maps : Set.MapsTo α (Set.Icc 0 1) (Set.Icc 0 1))
    {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (hnn : ∀ i, μ i (Set.Iio 0) = 0) (hfin : Emax μ < ⊤) :
    Tendsto (fun m : ℕ => detBlindValue α (padZero μ m)) atTop (𝓝 (blindValue α μ)) := by sorry

end BlindProphetSec.Blind
