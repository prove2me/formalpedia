-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_Ctx_merge_spec
-- name    : BCFGJPSSV26.Greedy.Ctx.merge_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:40:36.15806+00:00
-- url     : https://prove2.me/theorems/d7858f00-1839-465c-bebf-87ca8b40263c
-- title:
--   Correctness of the merge: a valid solution with exactly $k$ regular facilities and few free copies
-- statement:
--   This is the correctness of the merge of the log-adaptive greedy algorithm (Appendix D.1 of Part I, after [CGLSS25, Section 3.5]): it ends with a valid solution that has exactly $k$ regular facilities and at most three free copies per sequence.
--
--   **Setting.** There are $n\ge2$ clients and $m$ facilities in a pseudometric space with rational distances; the client–facility distances satisfy $1\le d(j,i)\le M$ and are stored in a table, and $1\le k<\min(n,m)$. The parameters satisfy $0<\delta\le\tfrac1{100}$, $0<\varepsilon\le\tfrac{\delta}{10}$, $\eta=\tfrac{\delta^2}{100n^2}$, $n\eta\le\tfrac{\delta\varepsilon}{10}$, $M\ge1$, $R\ge1$, $4nM+\gamma M\le\theta_{R-1}$, $K=2\theta_R$ and $L\ge m+4$, where $\theta_r=(1+\varepsilon^2)^r$ and $\gamma=\tfrac{153}{125}$. The grids $\hat f_b=\delta+(4nM-\delta)\,b/2^{P_f}$ of opening costs and $u_g=Kg/2^{P_u}$ of offsets have steps at most $\eta$.
--
--   The atom $(i,0)$ is the regular facility $i$, and $(i,g+1)$ is a free copy of facility $i$ at offset $u_g$; an atom is *in range* if $i<m$ and $g\le2^{P_u}$. The *profile* of a list $S$ of atoms is $D_S(j)=\min\bigl(K,\ \min_{(i,u)}(d(j,i)+u)\bigr)$, over the pairs $(i,u)$ (facility, offset) of the atoms of $S$.
--
--   **Notions** (Part I, Definitions D.2, D.3 and D.6). Sequence $p$, counted from $0$, has type 1 if $p$ is even and type 2 if $p$ is odd, and runs at time $\theta_{\lfloor p/2\rfloor}$. For an opening cost $f$ and a slack $\eta'$, an atom is *valid* after a list $A$ of atoms if it is free, or its facility is $(\text{type},\eta')$-openable for the profile of a finite set of pairs, with offsets $\ge0$, that contains the pairs of $A$. A *valid sequence* of type $p$ after $A$ is a list $W$ of atoms, each valid after $A$ followed by the atoms of $W$ before it, such that no facility is $(\text{type},0)$-openable for the profile of $A$ followed by $W$. A list of sequences is *$\eta'$-valid* if each sequence $p$ of it is a valid sequence of type $p$ after the atoms of the earlier ones. It is an *$\eta'$-valid solution* if moreover it has exactly $2R$ sequences, all offsets lie in $[0,K]$, and every client is inactive at the end: $(1-\delta)D(j)\le\theta_R$ for the final profile $D$.
--
--   **The merge.** Let $H_b$ be the greedy solution for the opening cost $\hat f_b$: $2R$ sequences, each built by opening as a regular atom, $L$ times, the first facility that passes the exact openability test. Bisection on $b\le2^{P_f}$ returns $H_0$ if it has at most $k$ regular atoms, some $H_b$ with exactly $k$ if one is met, and otherwise two solutions at adjacent grid points with more and fewer than $k$. Then the phases $p=0,\dots,2R-1$ act on a pair of solutions: step A completes the first $p$ sequences of the dominant one followed by sequence $p$ of the other; step B walks this sequence towards the greedy one by appending a free copy, deleting atoms and completing again; step C removes extra facilities; a binary search on the grid of offsets places a new free copy. A phase ends the merge when it meets a solution with exactly $k$ regular atoms, and otherwise passes a pair on. The merge returns a solution $H$ and a grid index $b$.
--
--   **Statement.** The output $(H,b)$ of the merge satisfies:
--
--   1. $H$ is an $\eta$-valid solution for the opening cost $\hat f_b$;
--   2. all atoms of $H$ are in range, and $b\le2^{P_f}$;
--   3. every sequence of $H$ contains at most three free atoms;
--   4. with $r(H)$ the number of regular atoms of $H$,
--   $$r(H)=k\qquad\text{or}\qquad\bigl(r(H)\le k,\ b=0,\ \text{and } H \text{ has no free atom}\bigr);$$
--   5. $r(H)\ge1$.
--
--   The proof of the core theorem (Theorem 5.16 of Part I) applies the robust LMP guarantee (Theorem D.7) to this solution: with exactly $k$ regular facilities the opening costs cancel, and there are at most $6R$ free copies in total.
--
--   **Formalization Note** Openability is that of Definition D.2 with the bid $\beta(x,y)=\max(x-\gamma y,0)$, type 2 being restricted to the bids $\min\{T,(1-\delta)d(j,S),(1+\varepsilon)\theta-d(j,i)\}$, $T\in[\theta,(1+\varepsilon^2)\theta]$, on the active clients within $\varepsilon\theta$ of $i$ (and $\theta$ on the other active clients). Atoms are pairs of natural numbers, decoded with the facility index modulo $m$. Table lookups default to $0$ out of range and are assumed nonnegative.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Appendix D.1; [CGLSS25, Section 3.5]. Lean source: `BCFGJPSSV26.Greedy.Ctx.merge_spec`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Alg/Merge.lean#L836-L841

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_MergeWalk
public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Merge

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Greedy

namespace Ctx

variable {C : Ctx} {X : Space C.ip.n C.ip.m} (hX : C.Hyp X)

theorem merge_spec : GoodOut hX C.merge.1 C.merge.2 := by sorry

end Ctx
end BCFGJPSSV26.Greedy
end
