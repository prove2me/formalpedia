-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_Ctx_MergeH_complete_sol_pre
-- name    : BCFGJPSSV26.Greedy.Ctx.MergeH.complete_sol_pre
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:39:24.477296+00:00
-- url     : https://prove2.me/theorems/62a52124-7fbb-4f9c-bf51-26ad8dea158a
-- title:
--   Completing a valid sequence after a valid prefix gives an $\eta$-valid solution
-- statement:
--   This is Observation D.8 of Part I in the form the merge uses: a valid prefix of $p$ sequences followed by one more valid sequence is completed by CompleteSolution to a valid solution.
--
--   **Setting.** There are $n\ge2$ clients and $m$ facilities in a pseudometric space with rational distances; the client–facility distances satisfy $1\le d(j,i)\le M$ and are stored in a table, and $1\le k<\min(n,m)$. The parameters satisfy $0<\delta\le\tfrac1{100}$, $0<\varepsilon\le\tfrac{\delta}{10}$, $\eta=\tfrac{\delta^2}{100n^2}$, $n\eta\le\tfrac{\delta\varepsilon}{10}$, $M\ge1$, $R\ge1$, $4nM+\gamma M\le\theta_{R-1}$, $K=2\theta_R$ and $L\ge m+4$, where $\theta_r=(1+\varepsilon^2)^r$ and $\gamma=\tfrac{153}{125}$. The grids $\hat f_b=\delta+(4nM-\delta)\,b/2^{P_f}$ of opening costs and $u_g=Kg/2^{P_u}$ of offsets have steps at most $\eta$.
--
--   The atom $(i,0)$ is the regular facility $i$, and $(i,g+1)$ is a free copy of facility $i$ at offset $u_g$; an atom is *in range* if $i<m$ and $g\le2^{P_u}$. The *profile* of a list $S$ of atoms is $D_S(j)=\min\bigl(K,\ \min_{(i,u)}(d(j,i)+u)\bigr)$, over the pairs $(i,u)$ (facility, offset) of the atoms of $S$.
--
--   **Notions** (Part I, Definitions D.2, D.3 and D.6). Sequence $p$, counted from $0$, has type 1 if $p$ is even and type 2 if $p$ is odd, and runs at time $\theta_{\lfloor p/2\rfloor}$. For an opening cost $f$ and a slack $\eta'$, an atom is *valid* after a list $A$ of atoms if it is free, or its facility is $(\text{type},\eta')$-openable for the profile of a finite set of pairs, with offsets $\ge0$, that contains the pairs of $A$. A *valid sequence* of type $p$ after $A$ is a list $W$ of atoms, each valid after $A$ followed by the atoms of $W$ before it, such that no facility is $(\text{type},0)$-openable for the profile of $A$ followed by $W$. A list of sequences is *$\eta'$-valid* if each sequence $p$ of it is a valid sequence of type $p$ after the atoms of the earlier ones. It is an *$\eta'$-valid solution* if moreover it has exactly $2R$ sequences, all offsets lie in $[0,K]$, and every client is inactive at the end: $(1-\delta)D(j)\le\theta_R$ for the final profile $D$.
--
--   **CompleteSequence** (of type $\nu$, for the opening cost $f$ at time $\theta$, after a list $A$ of atoms, from a list $W$) repeats $L$ times: if some facility passes the exact test of type $\nu$, an exact rational computation, for the profile of $A$ followed by $W$, the regular atom of the one of least index is appended to $W$. Write $\mathrm{CS}_p(f;A,W)$ for the result with the type and the time $\theta_{\lfloor p/2\rfloor}$ of sequence $p$.
--
--   **CompleteSolution** (for the opening cost $f$, on a list $H$ of sequences): for $p=0,\dots,2R-1$ in turn, if the current list has exactly $p$ sequences, the sequence $\mathrm{CS}_p(f;A,\emptyset)$ is appended, where $A$ lists all atoms present.
--
--   **Statement.** Let $p<2R$ and $b\le2^{P_f}$. Let $H$ be a list of exactly $p$ sequences of atoms in range that is $\eta$-valid for the opening cost $\hat f_b$, and let $W$ be a list of atoms in range that is a valid sequence of type $p$ after the atoms of $H$, for $\hat f_b$ and the slack $\eta$. Write $H\cdot W$ for $H$ with $W$ appended as sequence $p$. Then:
--
--   1. the completion is a solution:
--   $$\mathrm{CompleteSolution}(\hat f_b;\ H\cdot W)\ \text{ is an } \eta\text{-valid solution for the opening cost } \hat f_b;$$
--   2. all its atoms are in range.
--
--   Every solution that the merge examines in phase $p$ (Appendix D.1 of Part I) has this form: the common prefix, a modified sequence $p$, and the greedy completion. The lemma makes each of them a valid solution, to which the robust LMP guarantee (Theorem D.7) applies once the number of regular facilities is $k$.
--
--   **Formalization Note** Openability is that of Definition D.2 with the bid $\beta(x,y)=\max(x-\gamma y,0)$, type 2 being restricted to the bids $\min\{T,(1-\delta)d(j,S),(1+\varepsilon)\theta-d(j,i)\}$, $T\in[\theta,(1+\varepsilon^2)\theta]$, on the active clients within $\varepsilon\theta$ of $i$ (and $\theta$ on the other active clients). Atoms are pairs of natural numbers, decoded with the facility index modulo $m$. Table lookups default to $0$ out of range and are assumed nonnegative.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Observation D.8. Lean source: `BCFGJPSSV26.Greedy.Ctx.MergeH.complete_sol_pre`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Alg/MergeAux.lean#L642-L653

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

theorem complete_sol_pre (hlen : pre.length = p) (hp : p < 2 * C.ip.R) (hb : b ≤ 2 ^ C.ip.Pf)
    (hv : EtaValid C.par X.d (C.fhat b) C.ip.η (decH hX pre)) (hokp : C.SolOK pre)
    {W : List AAtom} (hW : VS hX p b pre W) (hok : ∀ a ∈ W, C.AtomOK a) :
    Sol C.par X.d (C.fhat b) C.ip.η (decH hX (C.complete (C.fhat b) (pre ++ [W]))) ∧
      C.SolOK (C.complete (C.fhat b) (pre ++ [W])) := by sorry

end BCFGJPSSV26.Greedy.Ctx.MergeH
end
