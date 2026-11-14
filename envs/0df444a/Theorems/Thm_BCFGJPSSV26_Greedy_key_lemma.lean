-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_key_lemma
-- name    : BCFGJPSSV26.Greedy.key_lemma
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:41:38.171831+00:00
-- url     : https://prove2.me/theorems/efa62a3c-05ee-41c1-a8c8-8f5998100814
-- title:
--   Key lemma: the overbidding of $i_0$ under the bids for $i$ is at most what $i_0$ collects with the same $T$
-- statement:
--   This is the key lemma on the one-parameter family of bids used by the type-2 openability test of the log-adaptive greedy of Part I: what a facility $i_0$ would be overpaid under the bids made for another facility $i$ is at most what $i_0$ itself collects with the same parameter $T$.
--
--   **Setting.** There are $n$ clients $j$ and $m$ facilities $i$ with rational distances $d(j,i)\ge 0$, and parameters $(\delta,\varepsilon,\eta_P,K,R)$ that are *good for $n$*: $0<\delta\le\frac{1}{100}$, $0<\varepsilon\le\frac{\delta}{10}$, $\eta_P\ge 0$, $n\,\eta_P\le\frac{\delta\varepsilon}{10}$ and $K\ge 2(1+\varepsilon^2)^R$. The bid is $\beta(x,y)=\max(x-\gamma y,\,0)$ with $\gamma=\frac{153}{125}$. Fix a time $\theta$ and a profile $D=(D_j)_j$ of rationals (the capped distances of the clients to the open set). The value of client $j$ is $v_j=\min\big(\theta,(1-\delta)D_j\big)$. For a facility $i$ and a parameter $T$, client $j$ bids
--
--   $$\tau_j^{i,T}=\min\big((1-\delta)D_j,\;g_j\big),\qquad g_j=\begin{cases}\max\big(\theta,\min(T,(1+\varepsilon)\theta-d(j,i))\big)&\text{if }d(j,i)\le\varepsilon\theta,\\ \theta&\text{otherwise.}\end{cases}$$
--
--   **Statement.** Assume the parameters are good for $n$, $d(j,i)\ge 0$ for all $j,i$, and $0<\theta\le T\le(1+\varepsilon^2)\theta$. Then for every profile $D$ and all facilities $i$ and $i_0$,
--
--   $$\sum_{j}\beta\big(\tau_j^{i,T},\,d(j,i_0)\big)\;\le\;\sum_{j}\beta\big(\min(T,(1-\delta)D_j),\,d(j,i_0)\big)\;\le\;\sum_{j}\beta\big(\tau_j^{i_0,T},\,(1-\tfrac{\delta}{2})\,d(j,i_0)\big).$$
--
--   The left side is the left side of condition (iv) of type-2 openability of $i$ (the overbidding of $i_0$ under the bids for $i$), and the right side is the left side of condition (iii) for $i_0$ (what $i_0$ collects in the metric scaled by $1-\frac{\delta}{2}$).
--
--   The lemma gives the pay-to-open lemma for these bids ([Part I, Lemma D.11]): without overbidding, if some facility can be paid for then some facility is openable. It also gives the step “increasing $\theta$” of the no-overbidding invariant ([Part I, Lemma E.6]). These are the two places where the analysis of Theorem 1.2 uses that no facility passes the type-2 test.
--
--   **Formalization Note** The distances are only assumed to be nonnegative rationals; no triangle inequality is used. The slack $\eta_P$ of the parameters enters only through the goodness conditions.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172). Lean source: `BCFGJPSSV26.Greedy.key_lemma`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Openable.lean#L466-L474

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Space
import Mathlib.Data.Finset.Max
public import Definitions.Def_BCFGJPSSV26_Greedy_Openable

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

variable {n m : ℕ} (P : Par) (d : Fin n → Fin m → ℚ)

variable {P d}

section Mono

variable {θ T T' f η : ℚ} {D D' : Fin n → ℚ} {i i₀ : Fin m}

end Mono

theorem key_lemma (hP : P.Good n) (hd : ∀ j i, 0 ≤ d j i) {θ T : ℚ} (hθ : 0 < θ) (hT : θ ≤ T)
    (hT' : T ≤ P.θplus θ) (D : Fin n → ℚ) (i i₀ : Fin m) :
    lhs4 P d θ D i T i₀ ≤ ∑ j, bid (min T ((1 - P.δ) * D j)) (d j i₀) ∧
      ∑ j, bid (min T ((1 - P.δ) * D j)) (d j i₀) ≤ lhs3 P d θ D i₀ T := by sorry

end BCFGJPSSV26.Greedy
end
