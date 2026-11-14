-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_Ctx_MergeH_walkB_spec
-- name    : BCFGJPSSV26.Greedy.Ctx.MergeH.walkB_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:39:46.417839+00:00
-- url     : https://prove2.me/theorems/45951680-ec81-4a59-b9fa-62981a01feb9
-- title:
--   The walk of step B of the merge: every point is a valid sequence, and the walk reaches the greedy sequence
-- statement:
--   This is the specification of the walk of step B of the merge (Appendix D.1 of Part I, after [CGLSS25, Section 3.5.2]): all its points are valid sequences with at most one free copy, consecutive points differ by one elementary move, and the last point extends the greedy sequence.
--
--   **Setting.** There are $n\ge2$ clients and $m$ facilities in a pseudometric space with rational distances; the client–facility distances satisfy $1\le d(j,i)\le M$ and are stored in a table, and $1\le k<\min(n,m)$. The parameters satisfy $0<\delta\le\tfrac1{100}$, $0<\varepsilon\le\tfrac{\delta}{10}$, $\eta=\tfrac{\delta^2}{100n^2}$, $n\eta\le\tfrac{\delta\varepsilon}{10}$, $M\ge1$, $R\ge1$, $4nM+\gamma M\le\theta_{R-1}$, $K=2\theta_R$ and $L\ge m+4$, where $\theta_r=(1+\varepsilon^2)^r$ and $\gamma=\tfrac{153}{125}$. The grids $\hat f_b=\delta+(4nM-\delta)\,b/2^{P_f}$ of opening costs and $u_g=Kg/2^{P_u}$ of offsets have steps at most $\eta$.
--
--   The atom $(i,0)$ is the regular facility $i$, and $(i,g+1)$ is a free copy of facility $i$ at offset $u_g$; an atom is *in range* if $i<m$ and $g\le2^{P_u}$. The *profile* of a list $S$ of atoms is $D_S(j)=\min\bigl(K,\ \min_{(i,u)}(d(j,i)+u)\bigr)$, over the pairs $(i,u)$ (facility, offset) of the atoms of $S$.
--
--   **Notions** (Part I, Definitions D.2, D.3 and D.6). Sequence $p$, counted from $0$, has type 1 if $p$ is even and type 2 if $p$ is odd, and runs at time $\theta_{\lfloor p/2\rfloor}$. For an opening cost $f$ and a slack $\eta'$, an atom is *valid* after a list $A$ of atoms if it is free, or its facility is $(\text{type},\eta')$-openable for the profile of a finite set of pairs, with offsets $\ge0$, that contains the pairs of $A$. A *valid sequence* of type $p$ after $A$ is a list $W$ of atoms, each valid after $A$ followed by the atoms of $W$ before it, such that no facility is $(\text{type},0)$-openable for the profile of $A$ followed by $W$. A list of sequences is *$\eta'$-valid* if each sequence $p$ of it is a valid sequence of type $p$ after the atoms of the earlier ones.
--
--   **CompleteSequence** (of type $\nu$, for the opening cost $f$ at time $\theta$, after a list $A$ of atoms, from a list $W$) repeats $L$ times: if some facility passes the exact test of type $\nu$, an exact rational computation, for the profile of $A$ followed by $W$, the regular atom of the one of least index is appended to $W$. Write $\mathrm{CS}_p(f;A,W)$ for the result with the type and the time $\theta_{\lfloor p/2\rfloor}$ of sequence $p$.
--
--   **The walk.** Let $H$ be a list of sequences with atoms $A$, let $H_p=\mathrm{CS}_p(\hat f_b;A,\emptyset)$ be the greedy sequence, and let $H'_p$ be a start. The walk keeps a current sequence $W$, initially $H'_p$, and records labelled *points*, the first being $(H'_p,\text{init})$. It makes $L$ rounds. A round does nothing if $H_p$ is a prefix of $W$. Otherwise let $q$ be the length of the common prefix of $H_p$ and $W$, and $z$ the facility of $H_p[q]$. The round appends the free copy $(z,1)$ of $z$ at offset $0$ (label *append-free*); then, $|W|-q$ times, it deletes the atom at position $q$ and completes the sequence by CompleteSequence, keeping at most $L$ atoms (label *remove-complete*); finally it replaces the atom at position $q$ by the regular atom $(z,0)$ (label *to-regular*).
--
--   **Statement.** Assume that $H$ has exactly $p$ sequences, is $\eta$-valid for the opening cost $\hat f_b$ and has its atoms in range, and that $H'_p$ is a valid sequence of type $p$ after $A$, for $\hat f_b$ and the slack $\eta$, whose atoms are regular and in range. Then:
--
--   1. the first point is $(H'_p,\text{init})$;
--   2. every point is a valid sequence of type $p$ after $A$, for $\hat f_b$ and $\eta$, with atoms in range and at most one free atom;
--   3. for consecutive points $S$, $S'$, the label of $S'$ is not init, and: for *append-free*, $S'=S\cdot(z,1)$ and all atoms of $S$ are regular; for *remove-complete*, $S=X\cdot h\cdot Y$ and $S'=X\cdot Y\cdot Z$ with $h$ and the atoms of $Z$ regular and at most one free atom in $X\cdot Y$; for *to-regular*, $S=B\cdot(z',1)\cdot B'$ and $S'=B\cdot(z',0)\cdot B'$ for some lists $B$, $B'$ and some $z'$;
--   4. the walk has a last point $S_{\mathrm{last}}$, and
--   $$H_p \text{ is a prefix of } S_{\mathrm{last}},\qquad \text{all atoms of } S_{\mathrm{last}} \text{ are regular}.$$
--
--   In a phase of the merge, the numbers of regular facilities of the completions of consecutive points are compared with $k$. By item 3 a change of side occurs at a move that step C or the offset search can refine, and by item 4 the walk ends at a sequence that differs from the greedy one only by extra facilities.
--
--   **Formalization Note** Openability is that of Definition D.2 with the bid $\beta(x,y)=\max(x-\gamma y,0)$, type 2 being restricted to the bids $\min\{T,(1-\delta)d(j,S),(1+\varepsilon)\theta-d(j,i)\}$, $T\in[\theta,(1+\varepsilon^2)\theta]$, on the active clients within $\varepsilon\theta$ of $i$ (and $\theta$ on the other active clients). In item 3, $z$, $X$, $h$, $Y$, $Z$ are the data recorded in the label of $S'$, and $\cdot$ is concatenation.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Appendix D.1; [CGLSS25, Section 3.5.2]. Lean source: `BCFGJPSSV26.Greedy.Ctx.MergeH.walkB_spec`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Alg/MergeWalk.lean#L357-L374

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

end Hp

theorem walkB_spec (hlen : pre.length = p)
    (hv : EtaValid C.par X.d (C.fhat b) C.ip.η (decH hX pre)) (hokp : C.SolOK pre)
    (hHp : Hp = C.completeSeq (typ1 p) (C.fhat b) (C.θseq p) pre.flatten [])
    (hH'p : VS hX p b pre H'p) (hok : ∀ a ∈ H'p, C.AtomOK a) (hreg : ∀ a ∈ H'p, a.2 = 0) :
    WInv hX p b pre H'p (C.walkB p (C.fhat b) pre Hp H'p) ∧
      ∃ cur κ, (C.walkB p (C.fhat b) pre Hp H'p).getLast? = some (cur, κ) ∧ Hp <+: cur ∧
        ∀ a ∈ cur, a.2 = 0 := by sorry

end BCFGJPSSV26.Greedy.Ctx.MergeH
end
