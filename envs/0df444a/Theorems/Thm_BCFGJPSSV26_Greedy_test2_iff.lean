-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_test2_iff
-- name    : BCFGJPSSV26.Greedy.test2_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:41:37.692746+00:00
-- url     : https://prove2.me/theorems/eed5bcef-eb0a-4b4e-8023-4da7accb40e2
-- title:
--   The type-2 openability test is exact: it accepts $i$ iff $i$ is $(2,0)$-openable
-- statement:
--   This result says that the closed-form test of type 2 used by the log-adaptive greedy of Part I decides exactly whether a facility is $(2,0)$-openable with the one-parameter family of bids (a restriction of [Part I, Definition D.2]).
--
--   **Setting.** There are $n$ clients $j$ and $m$ facilities $i$ with rational distances $d(j,i)\ge 0$, and parameters $(\delta,\varepsilon,\eta_P,K,R)$ that are *good for $n$*: $0<\delta\le\frac{1}{100}$, $0<\varepsilon\le\frac{\delta}{10}$, $\eta_P\ge 0$, $n\,\eta_P\le\frac{\delta\varepsilon}{10}$ and $K\ge 2(1+\varepsilon^2)^R$. The bid is $\beta(x,y)=\max(x-\gamma y,\,0)$ with $\gamma=\frac{153}{125}$. Fix a time $\theta$ and a profile $D=(D_j)_j$ of rationals (the capped distances of the clients to the open set). The value of client $j$ is $v_j=\min\big(\theta,(1-\delta)D_j\big)$. For a facility $i$ and a parameter $T$, client $j$ bids
--
--   $$\tau_j^{i,T}=\min\big((1-\delta)D_j,\;g_j\big),\qquad g_j=\begin{cases}\max\big(\theta,\min(T,(1+\varepsilon)\theta-d(j,i))\big)&\text{if }d(j,i)\le\varepsilon\theta,\\ \theta&\text{otherwise.}\end{cases}$$
--
--   Facility $i$ is *$(2,0)$-openable* for the opening cost $f$ if there is $T\in[\theta,(1+\varepsilon^2)\theta]$ with (iii) $\sum_j\beta\big(\tau_j^{i,T},(1-\frac{\delta}{2})d(j,i)\big)\ge f$ and (iv) $\sum_j\beta\big(\tau_j^{i,T},d(j,i_0)\big)\le f$ for every facility $i_0$.
--
--   **The test.** For an opening cost $f$ and a facility $i$, let $N=\{j: d(j,i)\le\varepsilon\theta,\ \theta<(1-\delta)D_j\}$ be the active clients near $i$, let $c_j=\min\big((1-\delta)D_j,(1+\varepsilon)\theta-d(j,i)\big)$, and let
--
--   $$\mathrm{need}=f-\sum_{j\notin N}\beta\big(v_j,(1-\tfrac{\delta}{2})d(j,i)\big)+\sum_{j\in N}\gamma\,(1-\tfrac{\delta}{2})\,d(j,i),\qquad T^{\ast}=\max\Big(\theta,\ \max_{j_0\in N}\frac{\mathrm{need}-\sum_{j\in N,\ c_j<c_{j_0}}c_j}{\lvert\{j\in N: c_j\ge c_{j_0}\}\rvert}\Big).$$
--
--   The test of type 2 accepts $i$ if $T^{\ast}\le(1+\varepsilon^2)\theta$ and, at $T=T^{\ast}$, $\sum_j\beta\big(\tau_j^{i,T^{\ast}},(1-\frac{\delta}{2})d(j,i)\big)\ge f$ and $\sum_j\beta\big(\tau_j^{i,T^{\ast}},d(j,i_0)\big)\le f$ for every facility $i_0$.
--
--   **Statement.** Assume the parameters are good for $n$, $d(j,i)\ge 0$ for all $j,i$, and $\theta>0$. Then for every rational $f$, every profile $D$ and every facility $i$,
--
--   $$\text{the test of type 2 accepts } i\quad\Longleftrightarrow\quad i\text{ is }(2,0)\text{-openable at time }\theta\text{ for the profile }D.$$
--
--   Hence the algorithm of Theorem 1.2 (and of Theorem 1.4) decides openability by exact rational arithmetic, without solving a linear program: an accepted facility is $(2,0)$-openable, and when no facility is accepted, none is openable with bids of this form, which is the maximality that the analysis of the greedy uses.
--
--   **Formalization Note** The test is a Boolean-valued function and the statement is that it returns true exactly when the openability predicate holds. $T^{\ast}$ is the least $T\ge\theta$ at which (iii) holds, if there is one. Distances are nonnegative rationals; no triangle inequality is assumed.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172). Lean source: `BCFGJPSSV26.Greedy.test2_iff`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Openable.lean#L599-L610

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

theorem test2_iff (hP : P.Good n) (hd : ∀ j i, 0 ≤ d j i) {f θ : ℚ} {D : Fin n → ℚ}
    {i : Fin m} (hθ : 0 < θ) : test2 P d f θ D i = true ↔ Open2 P d f 0 θ D i := by sorry

end BCFGJPSSV26.Greedy
end
