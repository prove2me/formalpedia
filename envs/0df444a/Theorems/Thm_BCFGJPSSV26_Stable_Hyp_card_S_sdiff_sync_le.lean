-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_Hyp_card_S_sdiff_sync_le
-- name    : BCFGJPSSV26.Stable.Hyp.card_S_sdiff_sync_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:49:01.693149+00:00
-- url     : https://prove2.me/theorems/e6d5c5ad-f07a-43a0-9126-5410172a1caa
-- title:
--   At most $s=632NL$ local-search centers are not partners of synced clusters
-- statement:
--   This is a second consequence of Lemma 4.2 of Part II: all but at most $s=632\,N\,L$ centers of the local-search solution are partners of synced optimal clusters.
--
--   **Standing hypotheses (H).** $I$ is a valid $k$-median instance ($n$ clients, $m$ facilities, rational pseudometric $d$) with $2\le k\le m$ and $\mathrm{opt}:=\mathrm{opt}_k>0$, where $\mathrm{opt}_\ell$ is the least cost of a nonempty set of at most $\ell$ facilities and $\mathrm{cost}(F)=\sum_j d(j,F)$. $N\ge 201$ is an integer and $\varepsilon=1/N$. $\beta>0$ is a real number, $I$ is $\beta$-stable, i.e. $\mathrm{opt}_{k-1}\ge(1+\beta)\,\mathrm{opt}_k$, and $L$ is a natural number with $L\ge 1/\beta$. $O$ is a set of exactly $k$ facilities with $\mathrm{cost}(O)=\mathrm{opt}$. $S$ is an approximate local optimum: $|S|=k$, and every nonempty set $T$ of at most $k$ facilities with $|S\setminus T|\le 24N$ satisfies $\mathrm{cost}(T)\ge\bigl(1-\tfrac{1}{Nk}\bigr)\mathrm{cost}(S)$.
--
--   For $c^\ast\in O$, $C^\ast$ denotes its optimal cluster (the clients whose nearest center of $O$ is $c^\ast$, ties going to the center of least index) and $\mathrm{cost}_{OPT}(C^\ast)=\sum_{j\in C^\ast}d(j,c^\ast)$. For $c\in S$, $C_c$ is the cluster of $c$ in $S$, defined in the same way, and $\mathrm{cost}_S(D)=\sum_{j\in D}d(j,S)$ for a set $D$ of clients. A center $c^\ast\in O$ is *synced* if some $c\in S$ satisfies $|C^\ast\,\triangle\,C_c|\le\varepsilon\,\min(|C^\ast|,|C_c|)$; $\sigma_{sync}(c^\ast)$ is one such $c$, chosen once and for all, and $O_{sync}$ is the set of synced centers of $O$. Let $s=632\,N\,L$. Then
--
--   $$\bigl|S\setminus\sigma_{sync}(O_{sync})\bigr|\;\le\;s .$$
--
--   The bound complements the one on the number of unsynced clusters. It is used to show that the set $LS_X\supseteq\sigma_{sync}(O_{sync})$ of substitutes known before the cluster sampling misses at most $s$ centers of $S$; hence every set $LS'$ with $LS_X\subseteq LS'\subseteq S$, in particular a good outcome of the cluster sampling, satisfies $|S\setminus LS'|\le s$, as the structural theorem requires.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), consequence of Lemma 4.2. Lean source: `BCFGJPSSV26.Stable.Hyp.card_S_sdiff_sync_le`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Stability/FewNotInSync.lean#L500-L513

module

public import Definitions.Def_BCFGJPSSV26_Stable_Stability_Defs
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_ThreeApprox
public import Definitions.Def_BCFGJPSSV26_Stable_Stability_FewNotInSync

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace FewNotInSync

variable (X : Ctx)

end FewNotInSync

namespace Hyp

variable {X : Ctx} (H : Hyp X)
include H

open FewNotInSync

theorem card_S_sdiff_sync_le : (X.S \ X.Osync.image X.σsync).card ≤ X.s := by sorry

end Hyp
end BCFGJPSSV26.Stable
end
