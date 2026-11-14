-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_ValidSeq_of_profile_le
-- name    : BCFGJPSSV26.Greedy.ValidSeq.of_profile_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:42:34.493881+00:00
-- url     : https://prove2.me/theorems/3828114d-f615-4587-9a29-6ded995e80b2
-- title:
--   A sequence of valid atoms whose profile is below that of a maximal sequence is a valid sequence
-- statement:
--   This result belongs to the validity calculus of the merge procedure of [Part I, Appendix D.1]: a sequence whose atoms are valid and whose profile is pointwise below the profile of a valid (hence maximal) sequence without overbidding is itself maximal, hence valid.
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
--   **Statement.** Assume the parameters are good for $n$ and $d(j,i)\ge 0$ for all $j,i$. Let $f,\eta$ be rationals, $p$ a sequence number, and $A,H,A',H'$ lists of atoms such that
--
--   1. $H$ is a valid sequence of type $p$ after $A$ (for $f$ and $\eta$);
--   2. there is no overbidding for $f$ at time $\theta_p$ for the profile of $A$ followed by $H$;
--   3. every atom of $H'$ satisfies the validity condition of a sequence of type $p$ after $A'$ (for $f$ and $\eta$), with respect to $A'$ and the atoms of $H'$ before it;
--   4. $D_{A'H'}(j)\le D_{AH}(j)$ for every client $j$, where $D_{AH}$ is the profile of $A$ followed by $H$.
--
--   Then
--
--   $$H'\ \text{ is a valid sequence of type }p\text{ after }A'\ (\text{for }f\text{ and }\eta).$$
--
--   In the merge of two greedy solutions in the proof of Theorem 1.2, sequences are modified (facilities removed and re-completed, free copies turned into regular facilities) in ways that do not raise the profile; this lemma shows that the modified sequences remain valid.
--
--   **Formalization Note** Sequences are counted from $0$ (type 1 for even $p$). The slack $\eta$ is a separate number from the $\eta_P$ of the parameters. Type-2 openability is the restricted one, with the one-parameter bids. Distances are nonnegative rationals.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172). Lean source: `BCFGJPSSV26.Greedy.ValidSeq.of_profile_le`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Valid.lean#L339-L346

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Openable
public import Definitions.Def_BCFGJPSSV26_Greedy_Valid

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

variable {n m : ℕ} (P : Par) (d : Fin n → Fin m → ℚ)

variable {P d}

theorem ValidSeq.of_profile_le (hP : P.Good n) (hd0 : ∀ j i, 0 ≤ d j i) {f η : ℚ} {p : ℕ}
    {pre pre' H H' : List (Atom m)} (hv : ValidSeq P d f η p pre H)
    (hno : NoOver P d f (P.θseq p) (profL P.K d (pre ++ H)))
    (hat : ∀ t (ht : t < H'.length), ValidAt P d f η p (pre' ++ H'.take t) H'[t])
    (hle : profL P.K d (pre' ++ H') ≤ profL P.K d (pre ++ H)) : ValidSeq P d f η p pre' H' := by sorry

end BCFGJPSSV26.Greedy
end
