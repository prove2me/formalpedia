-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_noOver_raise
-- name    : BCFGJPSSV26.Greedy.noOver_raise
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:41:47.966093+00:00
-- url     : https://prove2.me/theorems/ec988ab8-d4de-4342-951b-0d9173709ce3
-- title:
--   Raising the time from $\theta$ to $(1+\varepsilon^2)\theta$ keeps no overbidding after a maximal type-2 sequence
-- statement:
--   This is the step “increasing $\theta$” of [Part I, Lemma E.6]: if there is no overbidding at time $\theta$ and no facility is $(2,0)$-openable, then there is no overbidding at the raised time $(1+\varepsilon^2)\theta$.
--
--   **Setting.** There are $n$ clients $j$ and $m$ facilities $i$ with rational distances $d(j,i)\ge 0$, and parameters $(\delta,\varepsilon,\eta_P,K,R)$ that are *good for $n$*: $0<\delta\le\frac{1}{100}$, $0<\varepsilon\le\frac{\delta}{10}$, $\eta_P\ge 0$, $n\,\eta_P\le\frac{\delta\varepsilon}{10}$ and $K\ge 2(1+\varepsilon^2)^R$. The bid is $\beta(x,y)=\max(x-\gamma y,\,0)$ with $\gamma=\frac{153}{125}$. Fix a time $\theta$ and a profile $D=(D_j)_j$ of rationals (the capped distances of the clients to the open set). The value of client $j$ is $v_j=\min\big(\theta,(1-\delta)D_j\big)$. For a facility $i$ and a parameter $T$, client $j$ bids
--
--   $$\tau_j^{i,T}=\min\big((1-\delta)D_j,\;g_j\big),\qquad g_j=\begin{cases}\max\big(\theta,\min(T,(1+\varepsilon)\theta-d(j,i))\big)&\text{if }d(j,i)\le\varepsilon\theta,\\ \theta&\text{otherwise.}\end{cases}$$
--
--   For an opening cost $f$, facility $i$ is *$(2,0)$-openable* at time $\theta$ if for some $T\in[\theta,(1+\varepsilon^2)\theta]$ one has $\sum_j\beta\big(\tau_j^{i,T},(1-\frac{\delta}{2})d(j,i)\big)\ge f$ and $\sum_j\beta\big(\tau_j^{i,T},d(j,i_0)\big)\le f$ for every facility $i_0$.
--
--   **Statement.** Assume the parameters are good for $n$, $d(j,i)\ge 0$ for all $j,i$, and $\theta>0$. Let $f$ be an opening cost and $D$ a profile such that
--
--   - $\sum_j\beta\big(\min(\theta,(1-\delta)D_j),d(j,i_0)\big)\le f$ for every facility $i_0$ (no overbidding at time $\theta$), and
--   - no facility is $(2,0)$-openable at time $\theta$ for the profile $D$.
--
--   Then, for every facility $i_0$,
--
--   $$\sum_{j}\beta\Big(\min\big((1+\varepsilon^2)\theta,\,(1-\delta)D_j\big),\;d(j,i_0)\Big)\;\le\;f.$$
--
--   In the greedy algorithm the time is multiplied by $1+\varepsilon^2$ after each maximal sequence of type 2. This lemma is the inductive step that carries the no-overbidding invariant across the raise; the invariant gives the facility constraints of the factor-revealing program in the proof of the robust LMP guarantee ([Part I, Theorem D.7]).
--
--   **Formalization Note** Type-2 openability is the restricted one, with the one-parameter bids $\tau^{i,T}$; “no facility passes the exact type-2 test” is equivalent to the second hypothesis. Distances are nonnegative rationals.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Lemma E.6 (step “increasing θ”). Lean source: `BCFGJPSSV26.Greedy.noOver_raise`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Openable.lean#L685-L701

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

theorem noOver_raise (hP : P.Good n) (hd : ∀ j i, 0 ≤ d j i) {f θ : ℚ} {D : Fin n → ℚ}
    (hθ : 0 < θ) (hno : NoOver P d f θ D) (hmax : ∀ i, ¬ Open2 P d f 0 θ D i) :
    NoOver P d f (P.θplus θ) D := by sorry

end BCFGJPSSV26.Greedy
end
