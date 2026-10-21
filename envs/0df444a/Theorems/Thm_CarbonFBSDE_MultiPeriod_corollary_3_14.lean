-- Prove2me | Theorems.Thm_CarbonFBSDE_MultiPeriod_corollary_3_14
-- name    : CarbonFBSDE.MultiPeriod.corollary_3_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:38.199146+00:00
-- url     : https://prove2.me/theorems/5d1d5472-ce58-4354-922e-a97b482c822f
-- title:
--   Corollary 3.14, p. 25 — ψ(p,e,𝔢) = v^Φ(t₀,p,e,e) if e < Λ(𝔢), 1 otherwise, lies in 𝒦̂ (with r ≥ 0 and Γ → +∞ at −∞ added)
-- statement:
--   Let Assumption 1 hold, $\tau>0$, $\Phi\in\widehat{\mathcal K}$, $v^\Phi$ the value function of Corollary 3.12, $\Lambda\in\Theta$ and $t_0\in[0,\tau)$. Assume in addition $r\ge0$ and $\Lambda(\mathfrak e)-\mathfrak e\to+\infty$ as $\mathfrak e\to-\infty$. Define
--   $$\psi(p,e,\mathfrak e)=\begin{cases}v^\Phi(t_0,p,e,e)&\text{if }e<\Lambda(\mathfrak e),\\ 1&\text{otherwise.}\end{cases}\tag{3.55}$$
--   Then $\psi\in\widehat{\mathcal K}$.
--
--   This is the link between two trading periods: the price at the start of the next period, cut off at the penalty $1$ when the cap is exceeded, is again an admissible terminal condition.
--
--   **Formalization Note** Two hypotheses are **added** to the page's statement, and both are needed. (i) $r\ge0$: for $r<0$, $v^\Phi(t_0,p,e,e)\to e^{-r(\tau-t_0)}>1$ as $e\to+\infty$ (Proposition 3.5 (i)), so $\psi$ leaves $[0,1]$ and is not monotone. (ii) $\Gamma(\mathfrak e)=\Lambda(\mathfrak e)-\mathfrak e\to+\infty$ as $\mathfrak e\to-\infty$: if $\Gamma\le G$, then $\psi(p,e+\mathfrak e,\mathfrak e)=1$ for every $\mathfrak e$ once $e\ge G$, so the second requirement of $\widehat{\mathcal K}$ (infimum $0$) fails. The conclusion is $\psi\in\widehat{\mathcal K}$ for some Lipschitz constant.
-- source:
--   Chassagneux, Chotai & Crisan, Modelling multi-period carbon markets using singular forward-backward SDEs, arXiv:2008.09044v1, p. 25, Corollary 3.14, (3.55)

import Mathlib
import Definitions.Def_CarbonFBSDE_MultiPeriod_Model

open MeasureTheory ProbabilityTheory Filter Set EthierKurtz
open scoped NNReal ENNReal Topology

namespace CarbonFBSDE.MultiPeriod

theorem corollary_3_14 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (B : Basis d Ω)
    (hB : B.Valid) (c : Coeffs d) (L l1 l2 : ℝ) (hA : Assumption1 c L l1 l2) (r : ℝ)
    (hr : 0 ≤ r) (τ : ℝ≥0) (hτ : 0 < τ) (Φ : SDEState d → ℝ → ℝ → ℝ) (LΦ : ℝ)
    (hΦ : InKhat Φ LΦ) (v : ℝ≥0 → SDEState d → ℝ → ℝ → ℝ) (hv : IsValueFn B c r Φ τ v)
    (Λ : ℝ → ℝ) (hΛ : InTheta Λ) (hΛu : CapUnbounded Λ) (t0 : ℝ≥0) (ht0 : t0 < τ) :
    ∃ Lψ : ℝ, InKhat (fun p e ee => if e < Λ ee then v t0 p e e else 1) Lψ := by sorry

end CarbonFBSDE.MultiPeriod
