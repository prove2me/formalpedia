-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_Hyp_syncSub
-- name    : BCFGJPSSV26.Stable.Hyp.syncSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:49:13.035025+00:00
-- url     : https://prove2.me/theorems/8148fd72-82b0-4c0d-a491-543f600b07e0
-- title:
--   Proposition 4.3 (Part II) — substitutes for synced clusters
-- statement:
--   This is Proposition 4.3 of Part II: sending every synced optimal cluster to its partner in the local-search solution costs only slightly more than the optimum pays for these clusters.
--
--   **Standing hypotheses (H).** $I$ is a valid $k$-median instance ($n$ clients, $m$ facilities, rational pseudometric $d$) with $2\le k\le m$ and $\mathrm{opt}:=\mathrm{opt}_k>0$, where $\mathrm{opt}_\ell$ is the least cost of a nonempty set of at most $\ell$ facilities and $\mathrm{cost}(F)=\sum_j d(j,F)$. $N\ge 201$ is an integer and $\varepsilon=1/N$. $\beta>0$ is a real number, $I$ is $\beta$-stable, i.e. $\mathrm{opt}_{k-1}\ge(1+\beta)\,\mathrm{opt}_k$, and $L$ is a natural number with $L\ge 1/\beta$. $O$ is a set of exactly $k$ facilities with $\mathrm{cost}(O)=\mathrm{opt}$. $S$ is an approximate local optimum: $|S|=k$, and every nonempty set $T$ of at most $k$ facilities with $|S\setminus T|\le 24N$ satisfies $\mathrm{cost}(T)\ge\bigl(1-\tfrac{1}{Nk}\bigr)\mathrm{cost}(S)$.
--
--   For $c^\ast\in O$, $C^\ast$ denotes its optimal cluster (the clients whose nearest center of $O$ is $c^\ast$, ties going to the center of least index) and $\mathrm{cost}_{OPT}(C^\ast)=\sum_{j\in C^\ast}d(j,c^\ast)$. For $c\in S$, $C_c$ is the cluster of $c$ in $S$, defined in the same way, and $\mathrm{cost}_S(D)=\sum_{j\in D}d(j,S)$ for a set $D$ of clients. A center $c^\ast\in O$ is *synced* if some $c\in S$ satisfies $|C^\ast\,\triangle\,C_c|\le\varepsilon\,\min(|C^\ast|,|C_c|)$; $\sigma_{sync}(c^\ast)$ is one such $c$, chosen once and for all, and $O_{sync}$ is the set of synced centers of $O$. Then
--
--   $$\sum_{c^\ast\in O_{sync}}\ \sum_{j\in C^\ast} d\bigl(j,\sigma_{sync}(c^\ast)\bigr)\;\le\;(1+4\varepsilon)\sum_{c^\ast\in O_{sync}}\mathrm{cost}_{OPT}(C^\ast)\;+\;5\,\varepsilon\,\mathrm{cost}(S).$$
--
--   Together with Proposition 4.4 (close clusters) and the bound for the clusters missed by the client sampling, this gives the cost bound for the class $O_S$ of the structural theorem (Theorems 3.1 and 3.2): the clusters of $O_S$, sent to their substitutes, cost at most $(1+\eta)\sum_{O_S}\mathrm{cost}_{OPT}(C^\ast)+30\,\varepsilon\,\mathrm{opt}$, using $\mathrm{cost}(S)\le4\,\mathrm{opt}$. This is the row $1+\eta$ of $O_S$ in both bounds of the win-win argument.
--
--   **Formalization Note** The paper's $O(\varepsilon)$ terms are the explicit $4\varepsilon$ and $5\varepsilon$, with $\varepsilon=1/N$.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), Proposition 4.3. Lean source: `BCFGJPSSV26.Stable.Hyp.syncSub`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Stability/SyncSub.lean#L200-L233

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

theorem syncSub :
    ∑ c ∈ X.Osync, ∑ j ∈ X.C c, X.dist j (X.σsync c) ≤
      (1 + 4 * X.ε) * ∑ c ∈ X.Osync, X.costO c + 5 * X.ε * X.I.costF X.S := by sorry

end Hyp
end BCFGJPSSV26.Stable
end
