-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_Hyp_card_trialGood
-- name    : BCFGJPSSV26.Stable.Hyp.card_trialGood
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:48:12.795783+00:00
-- url     : https://prove2.me/theorems/460ad3dd-a005-4a75-ba83-96632f438b8f
-- title:
--   One trial of the algorithm is good with probability at least $N^{-200s}$ (Part II, Section 3.5)
-- statement:
--   The success probability of one trial of the algorithm of Part II (arXiv:2610.17172), following the combination of Section 3.5: under the standing hypotheses, at least a fraction $N^{-200s}$ of the random inputs of a trial makes the local search or one of the candidates of the trial cost at most $(1.89+1000/N)\,\mathrm{opt}$.
--
--   **Setting (the standing hypotheses of Part II, Sections 3–6).** Let $N\ge 201$ be an integer and $\varepsilon=1/N$. Let $I$ be a valid $k$-median instance (clients and $m$ facilities with a rational pseudometric $d$) with $2\le k\le m$ and $\mathrm{opt}:=\mathrm{opt}_k>0$, where $\mathrm{opt}_\ell$ is the least cost of a nonempty set of at most $\ell$ facilities. Assume $I$ is $\beta$-stable for some $\beta>0$, i.e. $\mathrm{opt}_{k-1}\ge(1+\beta)\,\mathrm{opt}_k$, and let $L\ge 1/\beta$ be a natural number. Put $s=632NL$ and $b=|\mathrm{enc}(I)|+7N$, where $|\mathrm{enc}(I)|$ is the length of the binary encoding of $I$. Let $O$ be a set of exactly $k$ facilities with $\mathrm{cost}(O)=\mathrm{opt}$, and let $S$ be an approximate local optimum: $|S|=k$, and $\mathrm{cost}(T)\ge\bigl(1-\tfrac{1}{Nk}\bigr)\mathrm{cost}(S)$ for every nonempty set $T$ of at most $k$ facilities with $|S\setminus T|\le 24N$.
--
--   **A trial.** Let $LS$ be a list of distinct facility indices (each less than $m$) whose set is $S$, and $B$ a natural number (the budget). A trial reads a vector $v$ of
--   $$C=6s+(20s+20)+k$$
--   chunks, each a number below $2^b$: the first $6s$ chunks drive the client sampling (Algorithm 1), which returns a list $\Lambda_1$ of dummies; the next $20s+20$ drive the cluster sampling (Algorithm 2), which returns the kept centers $LS'\subseteq LS$ and a list $\Lambda_2$ of dummies; the last $k$ color the centers of $LS'$ red or blue; and for every guess $p'\in\{0,\dots,s\}$ the submodular step (Section 5) for $LS'$, the dummies $\Lambda_1$ followed by $\Lambda_2$ and this coloring, with $N$ greedy rounds and enumerations cut at $B$, returns a candidate list of facilities or skips the guess. The trial is *good* if, for $T$ equal to $LS$ or to one of the candidates, the list $T$ made into exactly $k$ distinct facilities (keep its facilities once each, append the other facilities in increasing order, keep the first $k$) has
--   $$\mathrm{cost}\ \le\ \Bigl(1.89+\frac{1000}{N}\Bigr)\,\mathrm{opt}.$$
--
--   **Statement.** If $B\ge N^{s}$, then with $q=N^{-200s}$,
--   $$\#\bigl\{v\in\{0,\dots,2^b-1\}^{C}:\ \text{the trial on }v\text{ is good}\bigr\}\ \ge\ q\,\bigl(2^b\bigr)^{C}.$$
--
--   This is the per-trial bound behind Theorem 1.1: the algorithm runs $R=N^{200s+1}$ trials on disjoint blocks of coins, so some trial is good with probability at least $1-(1-q)^R\ge1-1/N$, and the output is at most as expensive as the local search and every candidate. The statement is where the process lemmas of the client sampling and of the cluster sampling, the color coding, the structural theorem (Theorems 3.1 and 3.2), the bound on the candidate (Theorem 3.4) and the win-win combination (Lemma 3.9) meet.
--
--   **Formalization Note** The statement counts chunk vectors of $b=|\mathrm{enc}(I)|+7N$ coin flips per chunk. The condition $B\ge N^s$ ensures that the greedy of the submodular step enumerates all its tuples. The hypotheses $k\ge2$ and $\mathrm{opt}>0$ are part of the setting; the cases $k=1$ and $\mathrm{opt}=0$ are treated separately by the local search alone.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), Section 3.5. Lean source: `BCFGJPSSV26.Stable.Hyp.card_trialGood`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Alg/Trial.lean#L256-L325

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClientSampling
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingAnalysis
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Submod
public import Definitions.Def_BCFGJPSSV26_Stable_Final_Combine
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Trial

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace Ctx

variable (X : Ctx)

end Ctx

open Classical in

theorem Hyp.card_trialGood {X : Ctx} (H : Hyp X) {LS : List ℕ} (hLS : X.I.centers LS = X.S)
    (hnd : LS.Nodup) (hm : ∀ i ∈ LS, i < X.I.m) {B : ℕ} (hB : X.P.N ^ X.s ≤ B) :
    X.P.q X.L * ((2 : ℝ) ^ X.b) ^ Par.Ctr X.P.N X.L X.I.k ≤
      (univ.filter fun v : Fin (Par.Ctr X.P.N X.L X.I.k) → Fin (2 ^ X.b) ↦
        TrialGood X.P X.I X.L LS B (toCh v)).card := by sorry

end BCFGJPSSV26.Stable
end
