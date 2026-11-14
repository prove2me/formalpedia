-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_Hyp_closeSub
-- name    : BCFGJPSSV26.Stable.Hyp.closeSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:49:10.513457+00:00
-- url     : https://prove2.me/theorems/8ec926fb-323f-4213-93b9-bdd1d73c1c36
-- title:
--   Proposition 4.4 (Part II) — substitutes for close clusters
-- statement:
--   This is Proposition 4.4 of Part II: a close optimal cluster, sent to the local-search center nearest to its center, costs at most about $1+\eta$ times its optimal cost.
--
--   **Standing hypotheses (H).** $I$ is a valid $k$-median instance ($n$ clients, $m$ facilities, rational pseudometric $d$) with $2\le k\le m$ and $\mathrm{opt}:=\mathrm{opt}_k>0$, where $\mathrm{opt}_\ell$ is the least cost of a nonempty set of at most $\ell$ facilities and $\mathrm{cost}(F)=\sum_j d(j,F)$. $N\ge 201$ is an integer and $\varepsilon=1/N$. $\beta>0$ is a real number, $I$ is $\beta$-stable, i.e. $\mathrm{opt}_{k-1}\ge(1+\beta)\,\mathrm{opt}_k$, and $L$ is a natural number with $L\ge 1/\beta$. $O$ is a set of exactly $k$ facilities with $\mathrm{cost}(O)=\mathrm{opt}$. $S$ is an approximate local optimum: $|S|=k$, and every nonempty set $T$ of at most $k$ facilities with $|S\setminus T|\le 24N$ satisfies $\mathrm{cost}(T)\ge\bigl(1-\tfrac{1}{Nk}\bigr)\mathrm{cost}(S)$.
--
--   For $c^\ast\in O$, $C^\ast$ denotes its optimal cluster (the clients whose nearest center of $O$ is $c^\ast$, ties going to the center of least index) and $\mathrm{cost}_{OPT}(C^\ast)=\sum_{j\in C^\ast}d(j,c^\ast)$. For $c\in S$, $C_c$ is the cluster of $c$ in $S$, defined in the same way, and $\mathrm{cost}_S(D)=\sum_{j\in D}d(j,S)$ for a set $D$ of clients. A center $c^\ast\in O$ is *synced* if some $c\in S$ satisfies $|C^\ast\,\triangle\,C_c|\le\varepsilon\,\min(|C^\ast|,|C_c|)$; $\sigma_{sync}(c^\ast)$ is one such $c$, chosen once and for all. A center $c^\ast\in O$ is *close* if it is not synced and $d(c^\ast,S)\le\eta\,\mathrm{avg}_{OPT}(C^\ast)+2\varepsilon\,\mathrm{avg}_S(C^\ast)$, where $\eta=89/100$, $\mathrm{avg}_{OPT}(C^\ast)=\mathrm{cost}_{OPT}(C^\ast)/|C^\ast|$ and $\mathrm{avg}_S(C^\ast)=\mathrm{cost}_S(C^\ast)/|C^\ast|$; $\sigma_{cl}(c^\ast)$ is the center of $S$ nearest to $c^\ast$ (of least index among the nearest ones). $O_{sync}$ and $O_{cl}$ are the sets of synced and of close centers. Then for every close center $c^\ast\in O_{cl}$,
--
--   $$\sum_{j\in C^\ast} d\bigl(j,\sigma_{cl}(c^\ast)\bigr)\;\le\;(1+\eta)\,\mathrm{cost}_{OPT}(C^\ast)\;+\;2\,\varepsilon\,\mathrm{cost}_S(C^\ast),\qquad \eta=\tfrac{89}{100}.$$
--
--   Together with Proposition 4.3 (synced clusters) this shows that the clusters of $O_{S0}=O_{sync}\cup O_{cl}$ have substitutes in $S$ at cost $(1+\eta)\,\mathrm{cost}_{OPT}+O(\varepsilon)\,\mathrm{opt}$; it enters the cost bound for the class $O_S$ in the structural theorem (Theorems 3.1 and 3.2). The constant $\eta=0.89$ is the source of the factor $1.89=1+\eta$ of the main theorem.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), Proposition 4.4. Lean source: `BCFGJPSSV26.Stable.Hyp.closeSub`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Stability/SyncSub.lean#L235-L257

module

public import Definitions.Def_BCFGJPSSV26_Stable_Stability_Defs
public import Definitions.Def_BCFGJPSSV26_Stable_Stability_SyncSub

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace Hyp

variable {X : Ctx} (H : Hyp X)
include H

theorem closeSub {c : Fin X.I.m} (hc : c ∈ X.Ocl) :
    ∑ j ∈ X.C c, X.dist j (X.σcl c) ≤ (1 + eta) * X.costO c + 2 * X.ε * X.costS (X.C c) := by sorry

end Hyp
end BCFGJPSSV26.Stable
end
