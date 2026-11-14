-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_Ctx_MergeH_noOver_pre
-- name    : BCFGJPSSV26.Greedy.Ctx.MergeH.noOver_pre
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:39:10.535928+00:00
-- url     : https://prove2.me/theorems/aa901159-f7df-4807-810e-065943ca94e2
-- title:
--   No overbidding after a valid prefix, for any atoms added
-- statement:
--   This is the no-overbidding invariant of the log-adaptive greedy algorithm (Lemma E.6 of Part I, with the inequality of Lemma D.9), in the form the merge uses: at the start of a sequence that follows a valid prefix, no facility is overbid, whatever atoms are added to the open set.
--
--   **Setting.** There are $n\ge2$ clients and $m$ facilities in a pseudometric space with rational distances; the client–facility distances satisfy $1\le d(j,i)\le M$ and are stored in a table, and $1\le k<\min(n,m)$. The parameters satisfy $0<\delta\le\tfrac1{100}$, $0<\varepsilon\le\tfrac{\delta}{10}$, $\eta=\tfrac{\delta^2}{100n^2}$, $n\eta\le\tfrac{\delta\varepsilon}{10}$, $M\ge1$, $R\ge1$, $4nM+\gamma M\le\theta_{R-1}$, $K=2\theta_R$ and $L\ge m+4$, where $\theta_r=(1+\varepsilon^2)^r$ and $\gamma=\tfrac{153}{125}$. The grids $\hat f_b=\delta+(4nM-\delta)\,b/2^{P_f}$ of opening costs and $u_g=Kg/2^{P_u}$ of offsets have steps at most $\eta$.
--
--   The atom $(i,0)$ is the regular facility $i$, and $(i,g+1)$ is a free copy of facility $i$ at offset $u_g$; an atom is *in range* if $i<m$ and $g\le2^{P_u}$. The *profile* of a list $S$ of atoms is $D_S(j)=\min\bigl(K,\ \min_{(i,u)}(d(j,i)+u)\bigr)$, over the pairs $(i,u)$ (facility, offset) of the atoms of $S$.
--
--   **Notions** (Part I, Definitions D.2, D.3 and D.6). Sequence $p$, counted from $0$, has type 1 if $p$ is even and type 2 if $p$ is odd, and runs at time $\theta_{\lfloor p/2\rfloor}$. For an opening cost $f$ and a slack $\eta'$, an atom is *valid* after a list $A$ of atoms if it is free, or its facility is $(\text{type},\eta')$-openable for the profile of a finite set of pairs, with offsets $\ge0$, that contains the pairs of $A$. A *valid sequence* of type $p$ after $A$ is a list $W$ of atoms, each valid after $A$ followed by the atoms of $W$ before it, such that no facility is $(\text{type},0)$-openable for the profile of $A$ followed by $W$. A list of sequences is *$\eta'$-valid* if each sequence $p$ of it is a valid sequence of type $p$ after the atoms of the earlier ones.
--
--   **Statement.** Let $p,b\in\mathbb N$, and let $H$ be a list of exactly $p$ sequences of atoms that is $\eta$-valid for the opening cost $\hat f_b$. Let $S$ be any finite list of facilities with rational offsets, and let $D$ be the profile of the atoms of $H$ together with $S$. Then, at the time $\theta=\theta_{\lfloor p/2\rfloor}$ of sequence $p$, for every facility $i_0$,
--
--   $$\sum_{j}\beta\bigl(\min(\theta,(1-\delta)D(j)),\ d(j,i_0)\bigr)\ \le\ \hat f_b,\qquad \beta(x,y)=\max(x-\gamma y,0).$$
--
--   In the correctness proof of the merge (Appendix D.1 of Part I) this inequality is the hypothesis under which maximality passes from a sequence to another one with a smaller profile. It is used when a free copy is appended, when the atoms of a sequence are replaced, and when the opening cost or an offset is changed (Claim D.12).
--
--   **Formalization Note** Openability is that of Definition D.2 with the bid $\beta(x,y)=\max(x-\gamma y,0)$, type 2 being restricted to the bids $\min\{T,(1-\delta)d(j,S),(1+\varepsilon)\theta-d(j,i)\}$, $T\in[\theta,(1+\varepsilon^2)\theta]$, on the active clients within $\varepsilon\theta$ of $i$ (and $\theta$ on the other active clients). The atoms of $H$ are pairs of natural numbers, decoded with the facility index modulo $m$; they need not be in range. No condition is imposed on $S$ or on $b$.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Lemmas E.6 and D.9. Lean source: `BCFGJPSSV26.Greedy.Ctx.MergeH.noOver_pre`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Alg/MergeAux.lean#L545-L550

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Complete
public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_MergeAux

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Greedy.Ctx.MergeH

section AtomsValid

variable {n m : ℕ} {P : Par} {d : Fin n → Fin m → ℚ} {f η : ℚ} {p : ℕ}

end AtomsValid

variable {C : Ctx}

variable {X : Space C.ip.n C.ip.m} (hX : C.Hyp X)

variable {p b : ℕ} {pre : List (List AAtom)}

theorem noOver_pre (hlen : pre.length = p)
    (hv : EtaValid C.par X.d (C.fhat b) C.ip.η (decH hX pre)) (S : List (Atom C.ip.m)) :
    NoOver C.par X.d (C.fhat b) (C.par.θseq p) (profL C.par.K X.d (decS hX pre.flatten ++ S)) := by sorry

end BCFGJPSSV26.Greedy.Ctx.MergeH
end
