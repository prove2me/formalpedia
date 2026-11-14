-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_Ctx_complete_sol
-- name    : BCFGJPSSV26.Greedy.Ctx.complete_sol
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:39:19.202721+00:00
-- url     : https://prove2.me/theorems/e9130705-fba6-4019-a282-ab001a5ee108
-- title:
--   Observation D.8 (Part I) — CompleteSolution produces an $\eta$-valid solution
-- statement:
--   This is Observation D.8 of Part I: the procedure CompleteSolution of the log-adaptive greedy algorithm turns a valid partial solution into a valid solution.
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
--   **Statement.** Let $f$ and $\eta'$ be rationals with $n\eta<f\le4nM$ and $\eta'\ge0$, and let $H$ be a list of at most $2R$ sequences of atoms in range that is $\eta'$-valid for the opening cost $f$. Then:
--
--   1. the completion is a solution:
--   $$\mathrm{CompleteSolution}(f;H)\ \text{ is an } \eta'\text{-valid solution for the opening cost } f;$$
--   2. all atoms of $\mathrm{CompleteSolution}(f;H)$ are in range.
--
--   With $H$ empty this gives the solutions of the greedy algorithm on the grid of opening costs. With $H$ a modified prefix it gives the solutions that the merge compares, phase after phase, in the proof of Theorem 5.16. The robust LMP guarantee (Theorem D.7 of Part I) is stated for such solutions.
--
--   **Formalization Note** Openability is that of Definition D.2 with the bid $\beta(x,y)=\max(x-\gamma y,0)$, type 2 being restricted to the bids $\min\{T,(1-\delta)d(j,S),(1+\varepsilon)\theta-d(j,i)\}$, $T\in[\theta,(1+\varepsilon^2)\theta]$, on the active clients within $\varepsilon\theta$ of $i$ (and $\theta$ on the other active clients). Atoms are pairs of natural numbers, decoded with the facility index modulo $m$. Table lookups default to $0$ out of range and are assumed nonnegative.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Observation D.8. Lean source: `BCFGJPSSV26.Greedy.Ctx.complete_sol`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Alg/Complete.lean#L612-L668

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Bridge
public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Complete

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Greedy

namespace Ctx

variable (C : Ctx)

variable {C} {X : Space C.ip.n C.ip.m} (hX : C.Hyp X)
include hX

section Iter

variable {b : Bool} {f θ : ℚ} {pre cur : List AAtom}

end Iter

theorem complete_sol {f η : ℚ} (hf : C.ip.n * C.ip.η < f) (hfM : f ≤ C.ip.fmax)
    (hη : 0 ≤ η) {H : List (List AAtom)} (hlen : H.length ≤ 2 * C.ip.R) (hok : C.SolOK H)
    (hv : EtaValid C.par X.d f η (decH hX H)) :
    Sol C.par X.d f η (decH hX (C.complete f H)) ∧ C.SolOK (C.complete f H) := by sorry

end Ctx
end BCFGJPSSV26.Greedy
end
