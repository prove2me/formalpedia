-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_Run_noOver_post
-- name    : BCFGJPSSV26.Greedy.Run.noOver_post
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:41:59.887627+00:00
-- url     : https://prove2.me/theorems/5d90366c-2f59-4148-9086-7cd607c2f42d
-- title:
--   No overbidding after every step of the execution of a valid greedy solution
-- statement:
--   This result is the no-overbidding invariant of the log-adaptive greedy ([Part I, Lemma E.6]) after every step of the execution of a valid solution, including after the last step and after a raise of the time.
--
--   **Setting.** A *run* consists of a pseudometric with rational values on $n$ clients and $m$ facilities with $d(j,i)\ge 1$ for every client $j$ and facility $i$; parameters $(\delta,\varepsilon,\eta,K,R)$ with $0<\delta\le\frac{1}{100}$, $0<\varepsilon\le\frac{\delta}{10}$, $\eta\ge 0$, $n\,\eta\le\frac{\delta\varepsilon}{10}$ and $K\ge 2(1+\varepsilon^2)^R$; an opening cost $f>n\eta$; and an $\eta$-valid solution $H=(H_0,\dots,H_{2R-1})$ for $f$ ([Part I, Definitions D.3 and D.6]): $2R$ valid and maximal sequences of atoms (regular facilities, or free copies of a facility at an offset $u\in[0,K]$), of type 1 for even and type 2 for odd index, after which every client is inactive. The *execution* is the list of steps that opens the atoms of $H_0,H_1,\dots$ in order and, after each sequence of type 2, has one step that raises the time from $\theta$ to $(1+\varepsilon^2)\theta$. A step $s$ of sequence $p$ has time $\theta_s=(1+\varepsilon^2)^{\lfloor p/2\rfloor}$ and sees the profile $D_s(j)=\min\big(K,\min_{(i,u)}(d(j,i)+u)\big)$, the minimum being over the atoms (facility $i$, offset $u$) opened before step $s$. The bid is $\beta(x,y)=\max(x-\gamma y,0)$ with $\gamma=\frac{153}{125}$.
--
--   For a step $s$, let $\theta_s^+$ be the time after it: $\theta_s^+=(1+\varepsilon^2)\theta_s$ if step $s$ raises the time and $\theta_s^+=\theta_s$ if it opens an atom. Let $D_{s+1}$ be the profile of the atoms opened up to and including step $s$.
--
--   **Statement.** For every step $s$ of the execution of a run and every facility $i_0$,
--
--   $$\sum_{j}\beta\Big(\min\big(\theta_s^{+},\,(1-\delta)\,D_{s+1}(j)\big),\;d(j,i_0)\Big)\;\le\;f,$$
--
--   where the sum is over all clients $j$.
--
--   In the proof of the robust LMP guarantee ([Part I, Theorem D.7]), a client that becomes inactive when the time is raised has its facility constraint in the factor-revealing program ([Part I, Lemma E.13]) from this inequality, with the raised time; for the other steps the inequality before the step is used.
--
--   **Formalization Note** The execution is a list of atomic steps (openings of atoms and raises of the time), and the statement is for every index $s$ smaller than the number of steps; for the last step, $\theta_s^+=(1+\varepsilon^2)^R$ and $D_{s+1}$ is the profile of the whole solution. All quantities are rational.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Lemma E.6. Lean source: `BCFGJPSSV26.Greedy.Run.noOver_post`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Trace.lean#L707-L719

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

theorem noOver_post {s : ℕ} (hs : s < R.len) :
    NoOver R.P R.X.d R.f (R.θpost s) (R.Dpre (s + 1)) := by sorry

end Run
end BCFGJPSSV26.Greedy
end
