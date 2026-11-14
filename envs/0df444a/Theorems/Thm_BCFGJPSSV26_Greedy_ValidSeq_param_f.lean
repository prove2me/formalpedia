-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_ValidSeq_param_f
-- name    : BCFGJPSSV26.Greedy.ValidSeq.param_f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:42:19.902046+00:00
-- url     : https://prove2.me/theorems/fd235f89-9416-4b51-97fb-784c610e5243
-- title:
--   Claim D.12 (Part I), first case — a $0$-valid sequence for $f'$ is $\eta$-valid for $f\in[f',f'+\eta]$
-- statement:
--   This is the first case of [Part I, Claim D.12] (changing the opening cost): a sequence that is valid with slack $0$ for the opening cost $f'$ is valid with slack $\eta$ for every opening cost between $f'$ and $f'+\eta$, provided there is no overbidding for $f'$.
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
--   An *atom* is a facility together with a rational offset and a flag (regular or free copy). The profile of a list or set $L$ of pairs is $D_L(j)=\min\big(K,\min_{(i,u)\in L}(d(j,i)+u)\big)$. Sequence number $p$ has type $\nu_p=1$ if $p$ is even and $\nu_p=2$ if $p$ is odd, and time $\theta_p=(1+\varepsilon^2)^{\lfloor p/2\rfloor}$. A list $H$ of atoms is a *valid sequence of type $p$ after* a list $A$ of atoms, for the opening cost $f$ and the slack $\eta$, if
--
--   - (validity) each atom of $H$ is a free copy, or its facility is $(\nu_p,\eta)$-openable at time $\theta_p$ for the profile $D_S$ of some finite set $S$ of pairs (facility, offset) with nonnegative offsets that contains the pairs of $A$ and of the atoms of $H$ before it;
--   - (maximality) no facility is $(\nu_p,0)$-openable at time $\theta_p$ for the profile of $A$ followed by $H$.
--
--   **Statement.** Assume the parameters are good for $n$, $d(j,i)\ge 0$ for all $j,i$, and $n\ge 1$. Let $f',f,\eta$ be rationals with
--
--   $$f'\le f\le f'+\eta,$$
--
--   let $p$ be a sequence number and $A$, $H$ lists of atoms such that
--
--   - $H$ is a valid sequence of type $p$ after $A$ for the opening cost $f'$ and the slack $0$, and
--   - there is no overbidding for $f'$ at time $\theta_p$ for the profile of $A$.
--
--   Then $H$ is a valid sequence of type $p$ after $A$ for the opening cost $f$ and the slack $\eta$.
--
--   The bisection of Theorem 1.2 produces greedy solutions for two opening costs that are adjacent on a grid of step at most $\eta$. In the first step of each phase of the merge, a sequence of one solution is reused at the opening cost of the other, and this lemma shows that it is $\eta$-valid there.
--
--   **Formalization Note** The endpoint $f=f'$ is allowed. Sequences are counted from $0$ (type 1 for even $p$). The slack $\eta$ is a separate number from the $\eta_P$ of the parameters. Type-2 openability is the restricted one, with the one-parameter bids.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Claim D.12 (first case). Lean source: `BCFGJPSSV26.Greedy.ValidSeq.param_f`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Valid.lean#L353-L375

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Openable
public import Definitions.Def_BCFGJPSSV26_Greedy_Valid

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

variable {n m : ℕ} (P : Par) (d : Fin n → Fin m → ℚ)

variable {P d}

theorem ValidSeq.param_f (hP : P.Good n) (hd0 : ∀ j i, 0 ≤ d j i) (hn : 1 ≤ n) {f f' η : ℚ}
    (hff : f' ≤ f) (hdiff : f - f' ≤ η) {p : ℕ} {pre H : List (Atom m)}
    (h0 : ValidSeq P d f' 0 p pre H) (hno : NoOver P d f' (P.θseq p) (profL P.K d pre)) :
    ValidSeq P d f η p pre H := by sorry

end BCFGJPSSV26.Greedy
end
