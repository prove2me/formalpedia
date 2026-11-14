-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_Ctx_MergeH_Hp_vs
-- name    : BCFGJPSSV26.Greedy.Ctx.MergeH.Hp_vs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:40:09.121911+00:00
-- url     : https://prove2.me/theorems/d8a94155-e691-4f2a-85a0-ad3522f723de
-- title:
--   The greedy completion of a prefix is a valid sequence
-- statement:
--   An instance of Observation D.8 of Part I used in the merge: the sequence that the greedy algorithm builds from the empty list after a prefix of sequences is a valid sequence.
--
--   **Setting.** There are $n\ge2$ clients and $m$ facilities in a pseudometric space with rational distances; the client–facility distances satisfy $1\le d(j,i)\le M$ and are stored in a table, and $1\le k<\min(n,m)$. The parameters satisfy $0<\delta\le\tfrac1{100}$, $0<\varepsilon\le\tfrac{\delta}{10}$, $\eta=\tfrac{\delta^2}{100n^2}$, $n\eta\le\tfrac{\delta\varepsilon}{10}$, $M\ge1$, $R\ge1$, $4nM+\gamma M\le\theta_{R-1}$, $K=2\theta_R$ and $L\ge m+4$, where $\theta_r=(1+\varepsilon^2)^r$ and $\gamma=\tfrac{153}{125}$. The grids $\hat f_b=\delta+(4nM-\delta)\,b/2^{P_f}$ of opening costs and $u_g=Kg/2^{P_u}$ of offsets have steps at most $\eta$.
--
--   The atom $(i,0)$ is the regular facility $i$, and $(i,g+1)$ is a free copy of facility $i$ at offset $u_g$; an atom is *in range* if $i<m$ and $g\le2^{P_u}$. The *profile* of a list $S$ of atoms is $D_S(j)=\min\bigl(K,\ \min_{(i,u)}(d(j,i)+u)\bigr)$, over the pairs $(i,u)$ (facility, offset) of the atoms of $S$.
--
--   **Notions** (Part I, Definitions D.2, D.3 and D.6). Sequence $p$, counted from $0$, has type 1 if $p$ is even and type 2 if $p$ is odd, and runs at time $\theta_{\lfloor p/2\rfloor}$. For an opening cost $f$ and a slack $\eta'$, an atom is *valid* after a list $A$ of atoms if it is free, or its facility is $(\text{type},\eta')$-openable for the profile of a finite set of pairs, with offsets $\ge0$, that contains the pairs of $A$. A *valid sequence* of type $p$ after $A$ is a list $W$ of atoms, each valid after $A$ followed by the atoms of $W$ before it, such that no facility is $(\text{type},0)$-openable for the profile of $A$ followed by $W$.
--
--   **CompleteSequence** (of type $\nu$, for the opening cost $f$ at time $\theta$, after a list $A$ of atoms, from a list $W$) repeats $L$ times: if some facility passes the exact test of type $\nu$, an exact rational computation, for the profile of $A$ followed by $W$, the regular atom of the one of least index is appended to $W$. Write $\mathrm{CS}_p(f;A,W)$ for the result with the type and the time $\theta_{\lfloor p/2\rfloor}$ of sequence $p$.
--
--   **Statement.** Let $p,b\in\mathbb N$, and let $H$ be a list of sequences of atoms in range, with $A$ the list of its atoms. Then
--
--   $$H_p:=\mathrm{CS}_p(\hat f_b;A,\emptyset)\ \text{ is a valid sequence of type } p \text{ after } A, \text{ for the opening cost } \hat f_b \text{ and the slack } \eta.$$
--
--   In phase $p$ of the merge (Appendix D.1 of Part I, after [CGLSS25, Section 3.5.2]), $H_p$ is sequence $p$ of the dominant solution and the target of the walk of step B. Its validity bounds its length by $m$, which makes the walk end, and gives the validity of the atom that the walk turns from a free copy into a regular facility.
--
--   **Formalization Note** Openability is that of Definition D.2 with the bid $\beta(x,y)=\max(x-\gamma y,0)$, type 2 being restricted to the bids $\min\{T,(1-\delta)d(j,S),(1+\varepsilon)\theta-d(j,i)\}$, $T\in[\theta,(1+\varepsilon^2)\theta]$, on the active clients within $\varepsilon\theta$ of $i$ (and $\theta$ on the other active clients). Atoms are pairs of natural numbers and sequences are lists. The number of sequences of $H$ and the validity of $H$ are not among the hypotheses.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Observation D.8. Lean source: `BCFGJPSSV26.Greedy.Ctx.MergeH.Hp_vs`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Alg/MergeWalk.lean#L126-L129

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_MergeAux
public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_MergeWalk

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Greedy.Ctx.MergeH

variable {C : Ctx}

variable {X : Space C.ip.n C.ip.m} (hX : C.Hyp X)

variable {p b : ℕ} {pre : List (List AAtom)} {Hp H'p : List AAtom}

section Hp

variable (hlen : pre.length = p) (hokp : C.SolOK pre)
  (hHp : Hp = C.completeSeq (typ1 p) (C.fhat b) (C.θseq p) pre.flatten [])

include hokp hHp in

theorem Hp_vs : VS hX p b pre Hp := by sorry

end Hp
end BCFGJPSSV26.Greedy.Ctx.MergeH
end
