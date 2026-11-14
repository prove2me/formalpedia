-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_noOver_partial
-- name    : BCFGJPSSV26.Greedy.noOver_partial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:42:01.444615+00:00
-- url     : https://prove2.me/theorems/354493a2-47e7-4a98-8b83-71f636e29474
-- title:
--   Lemmas E.6 and D.9 (Part I) — no overbidding at the start of every sequence, for every set of added atoms
-- statement:
--   This is the no-overbidding invariant of the log-adaptive greedy ([Part I, Lemmas E.6 and D.9]): after any number of valid sequences, at the time of the next sequence no facility is offered more than the opening cost, whatever atoms are added to the open set.
--
--   **Setting.** There are $n$ clients $j$ and $m$ facilities $i$ with rational distances $d(j,i)\ge 1$, and parameters $(\delta,\varepsilon,\eta_P,K,R)$ that are *good for $n$*: $0<\delta\le\frac{1}{100}$, $0<\varepsilon\le\frac{\delta}{10}$, $\eta_P\ge 0$, $n\,\eta_P\le\frac{\delta\varepsilon}{10}$ and $K\ge 2(1+\varepsilon^2)^R$. The bid is $\beta(x,y)=\max(x-\gamma y,\,0)$ with $\gamma=\frac{153}{125}$. Fix a time $\theta$ and a profile $D=(D_j)_j$ of rationals (the capped distances of the clients to the open set). The value of client $j$ is $v_j=\min\big(\theta,(1-\delta)D_j\big)$. For a facility $i$ and a parameter $T$, client $j$ bids
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
--   An *atom* is a facility together with a rational offset and a flag (regular or free copy). The profile of a list or set $L$ of pairs is $D_L(j)=\min\big(K,\min_{(i,u)\in L}(d(j,i)+u)\big)$. Sequence number $p$ has type $\nu_p=1$ if $p$ is even and $\nu_p=2$ if $p$ is odd, and time $\theta_p=(1+\varepsilon^2)^{\lfloor p/2\rfloor}$. A list $H$ of atoms is a *valid sequence of type $p$ after* a list $A$ of atoms, for the opening cost $f$ and the slack $\eta$, if
--
--   - (validity) each atom of $H$ is a free copy, or its facility is $(\nu_p,\eta)$-openable at time $\theta_p$ for the profile $D_S$ of some finite set $S$ of pairs (facility, offset) with nonnegative offsets that contains the pairs of $A$ and of the atoms of $H$ before it;
--   - (maximality) no facility is $(\nu_p,0)$-openable at time $\theta_p$ for the profile of $A$ followed by $H$.
--
--   **Statement.** Assume the parameters are good for $n$ and $d(j,i)\ge 1$ for all $j,i$. Let $f\ge 0$, let $\eta$ be any rational, and let $H_0,\dots,H_{q-1}$ be lists of atoms such that, for each $p<q$, $H_p$ is a valid sequence of type $p$ after $H_0,\dots,H_{p-1}$ (for $f$ and $\eta$). Then for every list $S$ of atoms and every facility $i_0$,
--
--   $$\sum_{j}\beta\Big(\min\big(\theta_q,\,(1-\delta)\,D(j)\big),\;d(j,i_0)\Big)\;\le\;f,\qquad \theta_q=(1+\varepsilon^2)^{\lfloor q/2\rfloor},$$
--
--   where $D$ is the profile of the atoms of $H_0,\dots,H_{q-1}$ together with those of $S$.
--
--   The invariant is used throughout the proof of Theorem 1.2: in the analysis it gives the facility constraints of the factor-revealing program for the robust LMP guarantee ([Part I, Theorem D.7]), and in the merge of two solutions it is the hypothesis under which changed sequences stay maximal.
--
--   **Formalization Note** Sequences are counted from $0$; sequence $p$ is of type 1 for even $p$, and the time is raised after each sequence of type 2. The slack $\eta$ of the validity is a separate number from the $\eta_P$ of the parameters, and $q$ is not required to be at most $2R$. Type-2 openability is the restricted one, with the one-parameter bids.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Lemmas E.6 and D.9. Lean source: `BCFGJPSSV26.Greedy.noOver_partial`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Valid.lean#L102-L146

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Openable
public import Definitions.Def_BCFGJPSSV26_Greedy_Valid

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

variable {n m : ℕ} (P : Par) (d : Fin n → Fin m → ℚ)

variable {P d}

theorem noOver_partial (hP : P.Good n) (hd1 : ∀ j i, 1 ≤ d j i) {f η : ℚ} (hf : 0 ≤ f)
    {Hp : List (List (Atom m))} (hv : EtaValid P d f η Hp) (S : List (Atom m)) :
    NoOver P d f (P.θseq Hp.length) (profL P.K d (Hp.flatten ++ S)) := by sorry

end BCFGJPSSV26.Greedy
end
