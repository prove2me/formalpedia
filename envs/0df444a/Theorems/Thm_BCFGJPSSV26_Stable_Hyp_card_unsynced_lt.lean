-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_Hyp_card_unsynced_lt
-- name    : BCFGJPSSV26.Stable.Hyp.card_unsynced_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:48:41.204295+00:00
-- url     : https://prove2.me/theorems/23383c36-d222-4488-aa35-68647c6ec50c
-- title:
--   Lemma 4.2 (Part II) — fewer than $632/(\varepsilon\beta)$ optimal clusters are not in sync
-- statement:
--   This is Lemma 4.2 of Part II with an explicit constant: on a $\beta$-stable instance, all but fewer than $632/(\varepsilon\beta)$ optimal clusters are synced with a cluster of the local-search solution.
--
--   **Standing hypotheses (H).** $I$ is a valid $k$-median instance ($n$ clients, $m$ facilities, rational pseudometric $d$) with $2\le k\le m$ and $\mathrm{opt}:=\mathrm{opt}_k>0$, where $\mathrm{opt}_\ell$ is the least cost of a nonempty set of at most $\ell$ facilities and $\mathrm{cost}(F)=\sum_j d(j,F)$. $N\ge 201$ is an integer and $\varepsilon=1/N$. $\beta>0$ is a real number, $I$ is $\beta$-stable, i.e. $\mathrm{opt}_{k-1}\ge(1+\beta)\,\mathrm{opt}_k$, and $L$ is a natural number with $L\ge 1/\beta$. $O$ is a set of exactly $k$ facilities with $\mathrm{cost}(O)=\mathrm{opt}$. $S$ is an approximate local optimum: $|S|=k$, and every nonempty set $T$ of at most $k$ facilities with $|S\setminus T|\le 24N$ satisfies $\mathrm{cost}(T)\ge\bigl(1-\tfrac{1}{Nk}\bigr)\mathrm{cost}(S)$.
--
--   For $c^\ast\in O$, $C^\ast$ denotes its optimal cluster (the clients whose nearest center of $O$ is $c^\ast$, ties going to the center of least index) and $\mathrm{cost}_{OPT}(C^\ast)=\sum_{j\in C^\ast}d(j,c^\ast)$. For $c\in S$, $C_c$ is the cluster of $c$ in $S$, defined in the same way, and $\mathrm{cost}_S(D)=\sum_{j\in D}d(j,S)$ for a set $D$ of clients. A center $c^\ast\in O$ is *synced* if some $c\in S$ satisfies $|C^\ast\,\triangle\,C_c|\le\varepsilon\,\min(|C^\ast|,|C_c|)$ (Definition 4.1). Then
--
--   $$\#\{c^\ast\in O:\ c^\ast\text{ is not synced}\}\;<\;\frac{632}{\varepsilon\,\beta}.$$
--
--   This is the point where stability enters the analysis. Since $L\ge 1/\beta$ and $\varepsilon=1/N$, the number $s=632\,N\,L$ used by the algorithm is at least $632/(\varepsilon\beta)$; so at most $s$ optimal clusters are special (neither synced nor close), and at most $s$ centers of $S$ are not partners of synced clusters. These bounds limit the number of dummies the samplings must find and the number of centers the algorithm closes, and hence the running time and the success probability $N^{-200s}$ of a trial.
--
--   **Formalization Note** Of the local search, the proof uses only $\mathrm{cost}(S)\le 4\,\mathrm{opt}$. The paper's bound $O(1/(\varepsilon\beta))$ is the explicit $632/(\varepsilon\beta)$.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), Lemma 4.2. Lean source: `BCFGJPSSV26.Stable.Hyp.card_unsynced_lt`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Stability/FewNotInSync.lean#L455-L486

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

open Classical in

theorem card_unsynced_lt : ((X.O.filter fun c ↦ ¬ X.IsSynced c).card : ℝ) < 632 / (X.ε * X.β) := by sorry

end Hyp
end BCFGJPSSV26.Stable
end
