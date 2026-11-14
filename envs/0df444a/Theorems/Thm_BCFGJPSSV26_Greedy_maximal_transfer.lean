-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_maximal_transfer
-- name    : BCFGJPSSV26.Greedy.maximal_transfer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:41:47.037197+00:00
-- url     : https://prove2.me/theorems/06b870a4-e97d-4180-882d-a56af9cce8a8
-- title:
--   Maximality transfers to smaller profiles and larger opening costs, without overbidding
-- statement:
--   This is the maximality part of [Part I, Claim D.12] (via Lemmas D.10 and D.11): if no facility is openable and there is no overbidding, then no facility is openable after the open set grows and the opening cost increases.
--
--   **Setting.** There are $n$ clients $j$ and $m$ facilities $i$ with rational distances $d(j,i)\ge 0$, and parameters $(\delta,\varepsilon,\eta_P,K,R)$ that are *good for $n$*: $0<\delta\le\frac{1}{100}$, $0<\varepsilon\le\frac{\delta}{10}$, $\eta_P\ge 0$, $n\,\eta_P\le\frac{\delta\varepsilon}{10}$ and $K\ge 2(1+\varepsilon^2)^R$. The bid is $\beta(x,y)=\max(x-\gamma y,\,0)$ with $\gamma=\frac{153}{125}$. Fix a time $\theta$ and a profile $D=(D_j)_j$ of rationals (the capped distances of the clients to the open set). The value of client $j$ is $v_j=\min\big(\theta,(1-\delta)D_j\big)$. For a facility $i$ and a parameter $T$, client $j$ bids
--
--   $$\tau_j^{i,T}=\min\big((1-\delta)D_j,\;g_j\big),\qquad g_j=\begin{cases}\max\big(\theta,\min(T,(1+\varepsilon)\theta-d(j,i))\big)&\text{if }d(j,i)\le\varepsilon\theta,\\ \theta&\text{otherwise.}\end{cases}$$
--
--   For an opening cost $f$ and a slack $\eta$, facility $i$ is
--
--   - *$(1,\eta)$-openable* if $\sum_j\beta\big(v_j,(1-\delta)\,d(j,i)\big)\ge f-n\eta$;
--   - *$(2,\eta)$-openable* if for some $T\in[\theta,(1+\varepsilon^2)\theta]$ both (iii) $\sum_j\beta\big(\tau_j^{i,T},(1-\frac{\delta}{2})\,d(j,i)\big)\ge f-n\eta$ and (iv) $\sum_j\beta\big(\tau_j^{i,T},d(j,i_0)\big)\le f$ for every facility $i_0$.
--
--   There is *no overbidding* if $\sum_j\beta\big(v_j,d(j,i_0)\big)\le f$ for every facility $i_0$.
--
--   **Statement.** Assume the parameters are good for $n$, $d(j,i)\ge 0$ for all $j,i$, and $\theta>0$. Let $\nu\in\{1,2\}$, let $f\le f'$ be opening costs and let $D'\le D$ be profiles (pointwise). Suppose that there is no overbidding for $f$ at time $\theta$ and profile $D$, and that no facility is $(\nu,0)$-openable for $f$ at time $\theta$ and profile $D$. Then
--
--   $$\text{no facility is }(\nu,0)\text{-openable for the opening cost }f'\text{ at time }\theta\text{ and profile }D'.$$
--
--   The merge of two greedy solutions in the proof of Theorem 1.2 changes sequences by adding free copies, moving offsets and changing the opening cost; each such change lowers the profile or raises the opening cost, and this lemma keeps the changed sequences maximal, hence valid.
--
--   **Formalization Note** Type-2 openability is the restricted one, with the one-parameter bids $\tau^{i,T}$. The type is a Boolean in the code. Distances are nonnegative rationals; no triangle inequality is assumed.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Claim D.12 (maximality part), via Lemmas D.10 and D.11. Lean source: `BCFGJPSSV26.Greedy.maximal_transfer`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Openable.lean#L667-L683

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

theorem maximal_transfer (hP : P.Good n) (hd : ∀ j i, 0 ≤ d j i) (b : Bool) {f f' θ : ℚ}
    {D D' : Fin n → ℚ} (hθ : 0 < θ) (hno : NoOver P d f θ D) (hD : D' ≤ D) (hf : f ≤ f')
    (hmax : ∀ i, ¬ OpenT P d b f 0 θ D i) : ∀ i, ¬ OpenT P d b f' 0 θ D' i := by sorry

end BCFGJPSSV26.Greedy
end
