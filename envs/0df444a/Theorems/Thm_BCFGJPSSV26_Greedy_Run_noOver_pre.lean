-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_Run_noOver_pre
-- name    : BCFGJPSSV26.Greedy.Run.noOver_pre
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:42:10.049589+00:00
-- url     : https://prove2.me/theorems/3307cc51-a80f-419e-acc7-2fbcf1d9c109
-- title:
--   No overbidding before every step of the execution of a valid greedy solution
-- statement:
--   This result is the no-overbidding invariant of the log-adaptive greedy ([Part I, Lemma E.6]) at every step of the execution of a valid solution: before each step, no facility is offered more than the opening cost by the current values of the clients.
--
--   **Setting.** A *run* consists of a pseudometric with rational values on $n$ clients and $m$ facilities with $d(j,i)\ge 1$ for every client $j$ and facility $i$; parameters $(\delta,\varepsilon,\eta,K,R)$ with $0<\delta\le\frac{1}{100}$, $0<\varepsilon\le\frac{\delta}{10}$, $\eta\ge 0$, $n\,\eta\le\frac{\delta\varepsilon}{10}$ and $K\ge 2(1+\varepsilon^2)^R$; an opening cost $f>n\eta$; and an $\eta$-valid solution $H=(H_0,\dots,H_{2R-1})$ for $f$ ([Part I, Definitions D.3 and D.6]): $2R$ valid and maximal sequences of atoms (regular facilities, or free copies of a facility at an offset $u\in[0,K]$), of type 1 for even and type 2 for odd index, after which every client is inactive. The *execution* is the list of steps that opens the atoms of $H_0,H_1,\dots$ in order and, after each sequence of type 2, has one step that raises the time from $\theta$ to $(1+\varepsilon^2)\theta$. A step $s$ of sequence $p$ has time $\theta_s=(1+\varepsilon^2)^{\lfloor p/2\rfloor}$ and sees the profile $D_s(j)=\min\big(K,\min_{(i,u)}(d(j,i)+u)\big)$, the minimum being over the atoms (facility $i$, offset $u$) opened before step $s$. The bid is $\beta(x,y)=\max(x-\gamma y,0)$ with $\gamma=\frac{153}{125}$.
--
--   **Statement.** For every step $s$ of the execution of a run and every facility $i_0$,
--
--   $$\sum_{j}\beta\Big(\min\big(\theta_s,\,(1-\delta)\,D_s(j)\big),\;d(j,i_0)\Big)\;\le\;f,$$
--
--   where the sum is over all clients $j$, $\theta_s$ is the time of step $s$ and $D_s$ is the profile of the atoms opened before step $s$.
--
--   In the proof of the robust LMP guarantee ([Part I, Theorem D.7]) this inequality, taken at the step at which a client becomes inactive, is the facility constraint of the factor-revealing program for that client ([Part I, Lemma E.13]); it is also used for [Part I, Lemma E.11].
--
--   **Formalization Note** The execution is a list of atomic steps (openings of atoms and raises of the time), and the statement is for every index $s$ smaller than the number of steps. The solution is valid with the restricted type-2 openability (one-parameter bids). All quantities are rational.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Lemma E.6. Lean source: `BCFGJPSSV26.Greedy.Run.noOver_pre`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Trace.lean#L698-L705

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

theorem noOver_pre {s : ℕ} (hs : s < R.len) : NoOver R.P R.X.d R.f (R.θs s) (R.Dpre s) := by sorry

end Run
end BCFGJPSSV26.Greedy
end
