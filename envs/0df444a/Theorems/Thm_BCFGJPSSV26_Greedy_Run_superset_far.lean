-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_Run_superset_far
-- name    : BCFGJPSSV26.Greedy.Run.superset_far
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:41:59.830414+00:00
-- url     : https://prove2.me/theorems/356acc49-d402-47ae-91db-9a2f7684ff6d
-- title:
--   Lemma E.11 (Part I) — a facility openable only for a strict superset is at distance $\ge\theta$ from the superset
-- statement:
--   This is [Part I, Lemma E.11]: in the execution of a valid solution of the log-adaptive greedy, a regular facility of a type-2 sequence that could be opened only with respect to a strict superset of the open set is at distance at least the current time from every element of that superset.
--
--   **Setting.** A *run* consists of a pseudometric with rational values on $n$ clients and $m$ facilities with $d(j,i)\ge 1$ for every client $j$ and facility $i$; parameters $(\delta,\varepsilon,\eta,K,R)$ with $0<\delta\le\frac{1}{100}$, $0<\varepsilon\le\frac{\delta}{10}$, $\eta\ge 0$, $n\,\eta\le\frac{\delta\varepsilon}{10}$ and $K\ge 2(1+\varepsilon^2)^R$; an opening cost $f>n\eta$; and an $\eta$-valid solution $H=(H_0,\dots,H_{2R-1})$ for $f$ ([Part I, Definitions D.3 and D.6]): $2R$ valid and maximal sequences of atoms (regular facilities, or free copies of a facility at an offset $u\in[0,K]$), of type 1 for even and type 2 for odd index, after which every client is inactive. The *execution* is the list of steps that opens the atoms of $H_0,H_1,\dots$ in order and, after each sequence of type 2, has one step that raises the time from $\theta$ to $(1+\varepsilon^2)\theta$. A step $s$ of sequence $p$ has time $\theta_s=(1+\varepsilon^2)^{\lfloor p/2\rfloor}$ and sees the profile $D_s(j)=\min\big(K,\min_{(i,u)}(d(j,i)+u)\big)$, the minimum being over the atoms (facility $i$, offset $u$) opened before step $s$. The bid is $\beta(x,y)=\max(x-\gamma y,0)$ with $\gamma=\frac{153}{125}$.
--
--   For a step $s$, a facility $i$, a finite set $S$ of pairs (facility, offset) and a parameter $T$, say that $(S,T)$ is a *witness* for $i$ at step $s$ if $S$ contains the pairs of the atoms opened before $s$, all offsets in $S$ are nonnegative, $\theta_s\le T\le(1+\varepsilon^2)\theta_s$, and with the profile $D_S(j)=\min\big(K,\min_{(i',u)\in S}(d(j,i')+u)\big)$ and the bids $\tau_j=\min\big((1-\delta)D_S(j),g_j\big)$, where $g_j=\max\big(\theta_s,\min(T,(1+\varepsilon)\theta_s-d(j,i))\big)$ if $d(j,i)\le\varepsilon\theta_s$ and $g_j=\theta_s$ otherwise, one has $\sum_j\beta\big(\tau_j,(1-\frac{\delta}{2})d(j,i)\big)\ge f-n\eta$ and $\sum_j\beta\big(\tau_j,d(j,i_0)\big)\le f$ for every facility $i_0$. Validity of the solution says that every regular atom of a type-2 sequence has a witness at its step.
--
--   **Statement.** Let step $s$ open a regular facility $i$ in a sequence of type 2, and suppose that there is no $T$ such that the set of pairs opened before $s$, with $T$, is a witness for $i$ at step $s$. Let $(\tilde S_s,T_s)$ be the witness for $i$ at step $s$ fixed by the formalization. Then for every pair $(i',u)\in\tilde S_s$,
--
--   $$\theta_s\;\le\;d(i,i')+u,$$
--
--   where $d(i,i')$ is the distance between the two facilities.
--
--   The lemma is used in the cost analysis under the event FREEZING ([Part I, Definition E.10 and Lemma E.12]), for the clients close to the facility opened when the last client of the group becomes inactive, in the proof of the robust LMP guarantee ([Part I, Theorem D.7]).
--
--   **Formalization Note** The witness $(\tilde S_s,T_s)$ is chosen once for each step (the set of pairs opened before the step whenever that works, otherwise an arbitrary witness); under the hypothesis it is an arbitrary but fixed witness. Type-2 openability is the restricted one, with the one-parameter bids.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Lemma E.11. Lean source: `BCFGJPSSV26.Greedy.Run.superset_far`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Trace.lean#L1105-L1150

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Structure
public import Mathlib.Data.Prod.Lex
public import Definitions.Def_BCFGJPSSV26_Greedy_Trace

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

namespace Run

variable {n m : ℕ} (R : Run n m)

theorem superset_far {s : ℕ} {a : Atom m} (hs : s < R.len) (hop : R.IsOp2 s a)
    (hstrict : ¬ ∃ T, R.WitOK s a (pairs (R.pre s)) T) :
    ∀ q ∈ (R.wit s).1, R.θs s ≤ R.X.dF a.fac q.1 + q.2 := by sorry

end Run
end BCFGJPSSV26.Greedy
end
