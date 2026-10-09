-- Prove2me | Theorems.Thm_DataDrivenRO_Marginal_theorem_7
-- name    : DataDrivenRO.Marginal.theorem_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T14:22:18.379626+00:00
-- url     : https://prove2.me/theorems/0ce6640c-fdd6-4007-9d2d-c839ad7ba094
-- title:
--   Theorem 7, p. 21 — w.p. ≥ 1 − α the order-statistic box 𝒰^M_ε satisfies δ*(v|𝒰^M_ε) ≥ VaR^{ℙ*}_ε(v) ∀v, and (29) holds
-- statement:
--   Let $d\ge1$, $0<\epsilon<1$, $0<\alpha<1$, and let $\mathbb P^*$ be a probability measure on $\mathbb R^d$ supported in a known box $[\hat{\mathbf u}^{(0)},\hat{\mathbf u}^{(N+1)}]$ with $\hat{\mathbf u}^{(0)}\le\hat{\mathbf u}^{(N+1)}$. Suppose the data $\mathcal S$ have an admissible law $Q$: the data are $N$ samples of each marginal, $\hat u^1_i,\dots,\hat u^N_i$ i.i.d. from $\mathbb P^*_i$ for each $i$, with arbitrary (unknown) dependence between the samples of different marginals. Let $\hat u^{(j)}_i$ be the order statistics of coordinate $i$, and let $s$ be the index of (26). Suppose $N-s+1<s$, and let
--   $$\mathcal U^M_\epsilon=\{\mathbf u\in\mathbb R^d:\hat u^{(N-s+1)}_i\le u_i\le\hat u^{(s)}_i,\ i=1,\dots,d\}.$$
--   Then:
--
--   1. with probability at least $1-\alpha$ over the sample,
--   $$\delta^*(\mathbf v\mid\mathcal U^M_\epsilon)\ge\mathrm{VaR}^{\mathbb P^*}_\epsilon(\mathbf v)\quad\text{for all }\mathbf v\in\mathbb R^d;$$
--   2. for every sample and every $\mathbf v$, $\displaystyle\delta^*(\mathbf v\mid\mathcal U^M_\epsilon)=\sum_{i=1}^d\max\big(v_i\hat u^{(N-s+1)}_i,v_i\hat u^{(s)}_i\big)$;
--   3. for every sample, $\mathcal U^M_\epsilon$ is nonempty, convex and compact.
--
--   By Theorem 1(a) of the paper, a nonempty convex compact set whose support function dominates $\mathrm{VaR}^{\mathbb P^*}_\epsilon$ in every direction implies a probabilistic guarantee at level $\epsilon$ for $\mathbb P^*$: every constraint $f(\mathbf u,\mathbf x)\le0$ with $f$ concave in $\mathbf u$ that holds robustly over the set holds with $\mathbb P^*$-probability at least $1-\epsilon$. Items 1 and 3 therefore give the paper's conclusion that, with probability at least $1-\alpha$, $\mathcal U^M_\epsilon$ implies a probabilistic guarantee for $\mathbb P^*$ at level $\epsilon$; item 2 is display (29).
--
--   **Formalization Note** The guarantee is stated in the support-function form of Theorem 1(a), whose equivalence with the guarantee is the goal of mission I of this series. The probability is under any law `Q` of the data `S : Fin N → Fin d → ℝ` with `IsMarginalSampleLaw Pstar Q`: each marginal's $N$ samples are i.i.d. from $\mathbb P^*_i$ and the coupling between marginals is arbitrary, as in §6 (joint i.i.d. draws are a special case). The probability of the event is its outer measure. The test is proved valid here, with no coverage hypothesis. The level $\epsilon$ is fixed: the family $\{\mathcal U^M_\epsilon\}$ need not work simultaneously (Remark 11). Coordinates are 0-based (`Fin d`), and $N-s+1$ is `N + 1 - s` in natural numbers.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem 7, p. 21 (proof EC.1.5, p. ec5)

import Mathlib
import Definitions.Def_DataDrivenRO_Marginal_Setting

open MeasureTheory

namespace DataDrivenRO.Marginal

/-- Theorem 7, p. 21 (proof EC.1.5, p. ec5). If `s` of (26) satisfies `N − s + 1 < s`, then with
probability at least `1 − α` over the sample, `δ*(v | 𝒰^M_ε) ≥ VaR^{ℙ*}_ε(v)` for every `v`
(the criterion of Theorem 1(a)); moreover (29) holds, and `𝒰^M_ε` is nonempty, convex and
compact for every sample. -/
theorem theorem_7 {d N : ℕ} (hd : 0 < d) (ε α : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hα0 : 0 < α) (hα1 : α < 1)
    (Pstar : Measure (Fin d → ℝ)) [IsProbabilityMeasure Pstar]
    (Q : Measure (Fin N → Fin d → ℝ)) (hQ : IsMarginalSampleLaw Pstar Q) (lo hi : Fin d → ℝ)
    (hlohi : lo ≤ hi) (hsupp : Pstar (box lo hi)ᶜ = 0)
    (hs : N + 1 - sIndex N d ε α < sIndex N d ε α) :
    ENNReal.ofReal (1 - α) ≤
        Q {S | ∀ v, VaR Pstar ε v ≤ RobustMDP.Shared.supportFunction (UM S lo hi ε α) v} ∧
      (∀ (S : Fin N → Fin d → ℝ) (v : Fin d → ℝ),
        RobustMDP.Shared.supportFunction (UM S lo hi ε α) v =
          ∑ i, max (v i * uhat S lo hi i (N + 1 - sIndex N d ε α))
            (v i * uhat S lo hi i (sIndex N d ε α))) ∧
      (∀ S : Fin N → Fin d → ℝ,
        (UM S lo hi ε α).Nonempty ∧ Convex ℝ (UM S lo hi ε α) ∧
          IsCompact (UM S lo hi ε α)) := by sorry

end DataDrivenRO.Marginal
