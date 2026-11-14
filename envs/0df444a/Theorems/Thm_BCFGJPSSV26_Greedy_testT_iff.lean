-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_testT_iff
-- name    : BCFGJPSSV26.Greedy.testT_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:41:39.009937+00:00
-- url     : https://prove2.me/theorems/3b8d9fd9-37f0-4f99-b4f4-0ea13b144311
-- title:
--   The openability tests of both types are exact: a test accepts $i$ iff $i$ is $(\nu,0)$-openable
-- statement:
--   This result combines the two exact tests of the log-adaptive greedy of Part I: for either type $\nu\in\{1,2\}$, the test of type $\nu$ accepts a facility exactly when it is $(\nu,0)$-openable.
--
--   **Setting.** There are $n$ clients $j$ and $m$ facilities $i$ with rational distances $d(j,i)\ge 0$, and parameters $(\delta,\varepsilon,\eta_P,K,R)$ that are *good for $n$*: $0<\delta\le\frac{1}{100}$, $0<\varepsilon\le\frac{\delta}{10}$, $\eta_P\ge 0$, $n\,\eta_P\le\frac{\delta\varepsilon}{10}$ and $K\ge 2(1+\varepsilon^2)^R$. The bid is $\beta(x,y)=\max(x-\gamma y,\,0)$ with $\gamma=\frac{153}{125}$. Fix a time $\theta$ and a profile $D=(D_j)_j$ of rationals (the capped distances of the clients to the open set). The value of client $j$ is $v_j=\min\big(\theta,(1-\delta)D_j\big)$. For a facility $i$ and a parameter $T$, client $j$ bids
--
--   $$\tau_j^{i,T}=\min\big((1-\delta)D_j,\;g_j\big),\qquad g_j=\begin{cases}\max\big(\theta,\min(T,(1+\varepsilon)\theta-d(j,i))\big)&\text{if }d(j,i)\le\varepsilon\theta,\\ \theta&\text{otherwise.}\end{cases}$$
--
--   For an opening cost $f$, facility $i$ is *$(1,0)$-openable* if $\sum_j\beta\big(v_j,(1-\delta)d(j,i)\big)\ge f$, and *$(2,0)$-openable* if there is $T\in[\theta,(1+\varepsilon^2)\theta]$ with $\sum_j\beta\big(\tau_j^{i,T},(1-\frac{\delta}{2})d(j,i)\big)\ge f$ and $\sum_j\beta\big(\tau_j^{i,T},d(j,i_0)\big)\le f$ for every facility $i_0$.
--
--   **The tests.** The test of type 1 accepts $i$ if $f\le\sum_j\beta\big(v_j,(1-\delta)d(j,i)\big)$. For the test of type 2, let $N=\{j:d(j,i)\le\varepsilon\theta,\ \theta<(1-\delta)D_j\}$, $c_j=\min\big((1-\delta)D_j,(1+\varepsilon)\theta-d(j,i)\big)$, $\mathrm{need}=f-\sum_{j\notin N}\beta\big(v_j,(1-\frac{\delta}{2})d(j,i)\big)+\sum_{j\in N}\gamma(1-\frac{\delta}{2})d(j,i)$ and $T^{\ast}=\max\big(\theta,\max_{j_0\in N}(\mathrm{need}-\sum_{j\in N,\,c_j<c_{j_0}}c_j)/\lvert\{j\in N:c_j\ge c_{j_0}\}\rvert\big)$; it accepts $i$ if $T^{\ast}\le(1+\varepsilon^2)\theta$ and the two inequalities of $(2,0)$-openability hold at $T=T^{\ast}$.
--
--   **Statement.** Assume the parameters are good for $n$, $d(j,i)\ge 0$ for all $j,i$, and $\theta>0$. Then for each type $\nu\in\{1,2\}$, every rational $f$, every profile $D$ and every facility $i$,
--
--   $$\text{the test of type }\nu\text{ accepts } i\quad\Longleftrightarrow\quad i\text{ is }(\nu,0)\text{-openable at time }\theta\text{ for the profile }D.$$
--
--   This is the form in which the algorithm is connected to the analysis: a sequence built by adding the first facility that passes the test until none does consists of openable facilities and is maximal, so the solutions of the greedy are valid in the sense of [Part I, Definitions D.3 and D.6] and the robust LMP guarantee applies to them.
--
--   **Formalization Note** The type is a Boolean (true for type 1, false for type 2) and each test is a Boolean-valued function; for type 1 the equivalence holds by definition. Distances are nonnegative rationals.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172). Lean source: `BCFGJPSSV26.Greedy.testT_iff`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Openable.lean#L612-L617

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

theorem testT_iff (hP : P.Good n) (hd : ∀ j i, 0 ≤ d j i) (b : Bool) {f θ : ℚ}
    {D : Fin n → ℚ} {i : Fin m} (hθ : 0 < θ) :
    testT P d b f θ D i = true ↔ OpenT P d b f 0 θ D i := by sorry

end BCFGJPSSV26.Greedy
end
