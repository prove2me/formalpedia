-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_Hyp_card_O1_le
-- name    : BCFGJPSSV26.Stable.Hyp.card_O1_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:48:53.288955+00:00
-- url     : https://prove2.me/theorems/2ed76bce-c131-4fda-840f-a3b6d277dde0
-- title:
--   At most $s=632NL$ optimal clusters are neither synced nor close
-- statement:
--   This is the consequence of Lemma 4.2 of Part II that the algorithm uses: the number of special optimal clusters, those that are neither synced nor close, is at most the parameter $s=632\,N\,L$.
--
--   **Standing hypotheses (H).** $I$ is a valid $k$-median instance ($n$ clients, $m$ facilities, rational pseudometric $d$) with $2\le k\le m$ and $\mathrm{opt}:=\mathrm{opt}_k>0$, where $\mathrm{opt}_\ell$ is the least cost of a nonempty set of at most $\ell$ facilities and $\mathrm{cost}(F)=\sum_j d(j,F)$. $N\ge 201$ is an integer and $\varepsilon=1/N$. $\beta>0$ is a real number, $I$ is $\beta$-stable, i.e. $\mathrm{opt}_{k-1}\ge(1+\beta)\,\mathrm{opt}_k$, and $L$ is a natural number with $L\ge 1/\beta$. $O$ is a set of exactly $k$ facilities with $\mathrm{cost}(O)=\mathrm{opt}$. $S$ is an approximate local optimum: $|S|=k$, and every nonempty set $T$ of at most $k$ facilities with $|S\setminus T|\le 24N$ satisfies $\mathrm{cost}(T)\ge\bigl(1-\tfrac{1}{Nk}\bigr)\mathrm{cost}(S)$.
--
--   For $c^\ast\in O$, $C^\ast$ denotes its optimal cluster (the clients whose nearest center of $O$ is $c^\ast$, ties going to the center of least index) and $\mathrm{cost}_{OPT}(C^\ast)=\sum_{j\in C^\ast}d(j,c^\ast)$. For $c\in S$, $C_c$ is the cluster of $c$ in $S$, defined in the same way, and $\mathrm{cost}_S(D)=\sum_{j\in D}d(j,S)$ for a set $D$ of clients. A center $c^\ast\in O$ is *synced* if some $c\in S$ satisfies $|C^\ast\,\triangle\,C_c|\le\varepsilon\,\min(|C^\ast|,|C_c|)$; $\sigma_{sync}(c^\ast)$ is one such $c$, chosen once and for all. A center $c^\ast\in O$ is *close* if it is not synced and $d(c^\ast,S)\le\eta\,\mathrm{avg}_{OPT}(C^\ast)+2\varepsilon\,\mathrm{avg}_S(C^\ast)$, where $\eta=89/100$, $\mathrm{avg}_{OPT}(C^\ast)=\mathrm{cost}_{OPT}(C^\ast)/|C^\ast|$ and $\mathrm{avg}_S(C^\ast)=\mathrm{cost}_S(C^\ast)/|C^\ast|$; $\sigma_{cl}(c^\ast)$ is the center of $S$ nearest to $c^\ast$ (of least index among the nearest ones). $O_{sync}$ and $O_{cl}$ are the sets of synced and of close centers. Let $O_1=O\setminus(O_{sync}\cup O_{cl})$ and $s=632\,N\,L$. Then
--
--   $$|O_1|\;\le\;s .$$
--
--   The clusters of $O_1$ are the ones that have no substitute in the local-search solution from the start; the client sampling and the cluster sampling of the algorithm handle them, by dummies, backups and satellites. The bound $|O_1|\le s$, with $s$ computable from the inputs $N$ and $L$, bounds the number of iterations of the two samplings and the sizes of the classes $O_\Lambda$, $O_P$, $O_R$ of the structural theorem (Theorems 3.1 and 3.2).
--
--   **Formalization Note** $s\ge 632/(\varepsilon\beta)$ because $\varepsilon=1/N$ and $L\ge 1/\beta$; the algorithm knows $L$, not $\beta$.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), consequence of Lemma 4.2. Lean source: `BCFGJPSSV26.Stable.Hyp.card_O1_le`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Stability/FewNotInSync.lean#L493-L498

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

theorem card_O1_le : X.O1.card ≤ X.s := by sorry

end Hyp
end BCFGJPSSV26.Stable
end
