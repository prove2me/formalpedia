-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_Ctx_MergeH_VS_of_pairs
-- name    : BCFGJPSSV26.Greedy.Ctx.MergeH.VS.of_pairs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:40:45.389034+00:00
-- url     : https://prove2.me/theorems/0d6635f7-ea88-4e6d-8e71-b83ebbe60332
-- title:
--   Valid atoms whose pairs contain those of a valid sequence form a valid sequence
-- statement:
--   A rule of the validity calculus of the merge (Appendix D.1 of Part I): after a valid prefix, a list of valid atoms that opens at least the pairs (facility, offset) of a valid sequence is itself a valid sequence.
--
--   **Setting.** There are $n\ge2$ clients and $m$ facilities in a pseudometric space with rational distances; the client–facility distances satisfy $1\le d(j,i)\le M$ and are stored in a table, and $1\le k<\min(n,m)$. The parameters satisfy $0<\delta\le\tfrac1{100}$, $0<\varepsilon\le\tfrac{\delta}{10}$, $\eta=\tfrac{\delta^2}{100n^2}$, $n\eta\le\tfrac{\delta\varepsilon}{10}$, $M\ge1$, $R\ge1$, $4nM+\gamma M\le\theta_{R-1}$, $K=2\theta_R$ and $L\ge m+4$, where $\theta_r=(1+\varepsilon^2)^r$ and $\gamma=\tfrac{153}{125}$. The grids $\hat f_b=\delta+(4nM-\delta)\,b/2^{P_f}$ of opening costs and $u_g=Kg/2^{P_u}$ of offsets have steps at most $\eta$.
--
--   The atom $(i,0)$ is the regular facility $i$, and $(i,g+1)$ is a free copy of facility $i$ at offset $u_g$; an atom is *in range* if $i<m$ and $g\le2^{P_u}$. The *profile* of a list $S$ of atoms is $D_S(j)=\min\bigl(K,\ \min_{(i,u)}(d(j,i)+u)\bigr)$, over the pairs $(i,u)$ (facility, offset) of the atoms of $S$.
--
--   **Notions** (Part I, Definitions D.2, D.3 and D.6). Sequence $p$, counted from $0$, has type 1 if $p$ is even and type 2 if $p$ is odd, and runs at time $\theta_{\lfloor p/2\rfloor}$. For an opening cost $f$ and a slack $\eta'$, an atom is *valid* after a list $A$ of atoms if it is free, or its facility is $(\text{type},\eta')$-openable for the profile of a finite set of pairs, with offsets $\ge0$, that contains the pairs of $A$. A *valid sequence* of type $p$ after $A$ is a list $W$ of atoms, each valid after $A$ followed by the atoms of $W$ before it, such that no facility is $(\text{type},0)$-openable for the profile of $A$ followed by $W$. A list of sequences is *$\eta'$-valid* if each sequence $p$ of it is a valid sequence of type $p$ after the atoms of the earlier ones.
--
--   **Statement.** Let $p,b\in\mathbb N$, and let $H$ be a list of exactly $p$ sequences of atoms that is $\eta$-valid for the opening cost $\hat f_b$, with $A$ the list of its atoms. Let $W$ be a valid sequence of type $p$ after $A$, for $\hat f_b$ and the slack $\eta$. Let $W'$ be a list of atoms, each valid (in sequence $p$, for $\hat f_b$ and $\eta$) after $A$ followed by the atoms of $W'$ before it, such that
--
--   $$\mathrm{pairs}(A)\cup\mathrm{pairs}(W)\ \subseteq\ \mathrm{pairs}(A)\cup\mathrm{pairs}(W').$$
--
--   Then $W'$ is a valid sequence of type $p$ after $A$, for $\hat f_b$ and $\eta$.
--
--   The merge uses this rule in step C, where facilities are removed from a completed sequence and a free copy is added: it shows that the intermediate sequences are valid, so that their completions are solutions.
--
--   **Formalization Note** Openability is that of Definition D.2 with the bid $\beta(x,y)=\max(x-\gamma y,0)$, type 2 being restricted to the bids $\min\{T,(1-\delta)d(j,S),(1+\varepsilon)\theta-d(j,i)\}$, $T\in[\theta,(1+\varepsilon^2)\theta]$, on the active clients within $\varepsilon\theta$ of $i$ (and $\theta$ on the other active clients). Atoms are pairs of natural numbers, decoded with the facility index modulo $m$; $\mathrm{pairs}$ is the set of pairs (facility, offset) of the decoded atoms. No range condition is imposed on the atoms or on $b$.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Appendix D.1. Lean source: `BCFGJPSSV26.Greedy.Ctx.MergeH.VS.of_pairs`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Alg/MergeAux.lean#L578-L586

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

theorem VS.of_pairs (hlen : pre.length = p)
    (hv : EtaValid C.par X.d (C.fhat b) C.ip.η (decH hX pre)) {H H' : List AAtom}
    (hH : VS hX p b pre H)
    (hat : AtomsValid C.par X.d (C.fhat b) C.ip.η p (decS hX pre.flatten) (decS hX H'))
    (hsub : pairs (decS hX pre.flatten ++ decS hX H) ⊆ pairs (decS hX pre.flatten ++ decS hX H')) :
    VS hX p b pre H' := by sorry

end BCFGJPSSV26.Greedy.Ctx.MergeH
end
