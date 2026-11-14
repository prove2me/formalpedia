-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_Ctx_completeSeq_validSeq
-- name    : BCFGJPSSV26.Greedy.Ctx.completeSeq_validSeq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:39:21.305192+00:00
-- url     : https://prove2.me/theorems/c21bc3a7-9457-415f-be05-ca3b24f2da00
-- title:
--   Observation D.8 (Part I) — CompleteSequence produces a valid sequence
-- statement:
--   This is Observation D.8 of Part I for one sequence: the procedure CompleteSequence of the log-adaptive greedy algorithm, started from a list of valid atoms, returns a valid sequence.
--
--   **Setting.** There are $n\ge2$ clients and $m$ facilities in a pseudometric space with rational distances; the client–facility distances satisfy $1\le d(j,i)\le M$ and are stored in a table, and $1\le k<\min(n,m)$. The parameters satisfy $0<\delta\le\tfrac1{100}$, $0<\varepsilon\le\tfrac{\delta}{10}$, $\eta=\tfrac{\delta^2}{100n^2}$, $n\eta\le\tfrac{\delta\varepsilon}{10}$, $M\ge1$, $R\ge1$, $4nM+\gamma M\le\theta_{R-1}$, $K=2\theta_R$ and $L\ge m+4$, where $\theta_r=(1+\varepsilon^2)^r$ and $\gamma=\tfrac{153}{125}$. The grids $\hat f_b=\delta+(4nM-\delta)\,b/2^{P_f}$ of opening costs and $u_g=Kg/2^{P_u}$ of offsets have steps at most $\eta$.
--
--   The atom $(i,0)$ is the regular facility $i$, and $(i,g+1)$ is a free copy of facility $i$ at offset $u_g$; an atom is *in range* if $i<m$ and $g\le2^{P_u}$. The *profile* of a list $S$ of atoms is $D_S(j)=\min\bigl(K,\ \min_{(i,u)}(d(j,i)+u)\bigr)$, over the pairs $(i,u)$ (facility, offset) of the atoms of $S$.
--
--   **Notions** (Part I, Definitions D.2, D.3 and D.6). Sequence $p$, counted from $0$, has type 1 if $p$ is even and type 2 if $p$ is odd, and runs at time $\theta_{\lfloor p/2\rfloor}$. For an opening cost $f$ and a slack $\eta'$, an atom is *valid* after a list $A$ of atoms if it is free, or its facility is $(\text{type},\eta')$-openable for the profile of a finite set of pairs, with offsets $\ge0$, that contains the pairs of $A$. A *valid sequence* of type $p$ after $A$ is a list $W$ of atoms, each valid after $A$ followed by the atoms of $W$ before it, such that no facility is $(\text{type},0)$-openable for the profile of $A$ followed by $W$.
--
--   **CompleteSequence** (of type $\nu$, for the opening cost $f$ at time $\theta$, after a list $A$ of atoms, from a list $W$) repeats $L$ times: if some facility passes the exact test of type $\nu$ for the profile of $A$ followed by $W$, the regular atom of the one of least index is appended to $W$. The test of type 1 checks $(1,0)$-openability directly; the test of type 2 computes in closed form a value $T^\star\ge\theta$ and checks $T^\star\le(1+\varepsilon^2)\theta$ and the two inequalities of $(2,0)$-openability at $T=T^\star$. Write $\mathrm{CS}_p(f;A,W)$ for the result with the type and the time $\theta_{\lfloor p/2\rfloor}$ of sequence $p$.
--
--   **Statement.** Let $f$ and $\eta'$ be rationals with $f>n\eta$ and $\eta'\ge0$, let $p\in\mathbb N$, and let $A$ and $W$ be lists of atoms in range such that every atom of $W$ is valid (in sequence $p$, for $f$ and $\eta'$) after $A$ followed by the atoms of $W$ before it. Then
--
--   $$\mathrm{CS}_p(f;A,W)\ \text{ is a valid sequence of type } p \text{ after } A, \text{ for the opening cost } f \text{ and the slack } \eta'.$$
--
--   CompleteSolution applies this with $W$ empty (Observation D.8 for solutions). The merge applies it each time it completes a modified sequence again, with a start $W$ that may contain free copies.
--
--   **Formalization Note** Openability is that of Definition D.2 with the bid $\beta(x,y)=\max(x-\gamma y,0)$, type 2 being restricted to the bids $\min\{T,(1-\delta)d(j,S),(1+\varepsilon)\theta-d(j,i)\}$, $T\in[\theta,(1+\varepsilon^2)\theta]$, on the active clients within $\varepsilon\theta$ of $i$ (and $\theta$ on the other active clients). Atoms are pairs of natural numbers, decoded with the facility index modulo $m$. Table lookups default to $0$ out of range and are assumed nonnegative.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Observation D.8. Lean source: `BCFGJPSSV26.Greedy.Ctx.completeSeq_validSeq`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Alg/Complete.lean#L550-L572

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

theorem completeSeq_validSeq {f η : ℚ} (hf : C.ip.n * C.ip.η < f) (hη : 0 ≤ η) {p : ℕ}
    {pre cur : List AAtom} (hok : ∀ a ∈ pre ++ cur, C.AtomOK a)
    (hcur : ∀ t (ht : t < cur.length), ValidAt C.par X.d f η p (decS hX (pre ++ cur.take t))
      (decA hX cur[t])) :
    ValidSeq C.par X.d f η p (decS hX pre)
      (decS hX (C.completeSeq (typ1 p) f (C.θseq p) pre cur)) := by sorry

end Ctx
end BCFGJPSSV26.Greedy
end
