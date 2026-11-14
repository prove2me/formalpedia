-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_Hyp_card_clientWitness
-- name    : BCFGJPSSV26.Stable.Hyp.card_clientWitness
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:43:27.060719+00:00
-- url     : https://prove2.me/theorems/6482dd33-5841-465c-88e3-5c3b953b43bc
-- title:
--   Client sampling (Part II, Section 4.2, Algorithm 1) — good outcomes have density at least $q_1^{2s}$
-- statement:
--   This is the process lemma of the client sampling: the client-sampling theorem of Part II (arXiv:2610.17172), Section 4.2, for Algorithm 1, with the lemma of its proof in Section 4.6, as a lower bound on the number of random inputs for which the sampling returns a good list of dummies.
--
--   **Setting (the standing hypotheses of Part II, Sections 3–6).** Let $N\ge 201$ be an integer and $\varepsilon=1/N$. Let $I$ be a valid $k$-median instance (clients and $m$ facilities with a rational pseudometric $d$) with $2\le k\le m$ and $\mathrm{opt}:=\mathrm{opt}_k>0$, where $\mathrm{opt}_\ell$ is the least cost of a nonempty set of at most $\ell$ facilities. Assume $I$ is $\beta$-stable for some $\beta>0$, i.e. $\mathrm{opt}_{k-1}\ge(1+\beta)\,\mathrm{opt}_k$, and let $L\ge 1/\beta$ be a natural number. Put $s=632NL$ and $b=|\mathrm{enc}(I)|+7N$, where $|\mathrm{enc}(I)|$ is the length of the binary encoding of $I$. Let $O$ be a set of exactly $k$ facilities with $\mathrm{cost}(O)=\mathrm{opt}$, and let $S$ be an approximate local optimum: $|S|=k$, and $\mathrm{cost}(T)\ge\bigl(1-\tfrac{1}{Nk}\bigr)\mathrm{cost}(S)$ for every nonempty set $T$ of at most $k$ facilities with $|S\setminus T|\le 24N$.
--
--   **Notation.** For $o\in O$: $C_o$ is its optimal cluster (the clients whose nearest facility of $O$ is $o$, ties going to the least index), $\mathrm{cost}_O(o)=\sum_{j\in C_o}d(j,o)$, $\mathrm{avg}_O(o)=\mathrm{cost}_O(o)/|C_o|$ and $\mathrm{avg}_S(o)=\frac{1}{|C_o|}\sum_{j\in C_o}d(j,S)$; $\mathrm{per}(o)$ is the $\varepsilon$-percentile, the least distance $t=d(j,o)$, $j\in C_o$, such that at least $\varepsilon|C_o|$ clients of $C_o$ are within $t$ of $o$; $\mathrm{core}_\gamma(o)=\{j\in C_o:\ d(j,o)\le(1+\gamma)\,\mathrm{per}(o)\}$; and $\kappa(o)$ is defined by $1+\kappa=(89-12t)/(65t)$ with $t=\max\bigl(\tfrac{89}{100},\min(1,x)\bigr)$, $x=\mathrm{per}(o)/\mathrm{avg}_O(o)$ ($x=1$ if $\mathrm{avg}_O(o)=0$). For a set $D$ of clients, $\mathrm{cost}_S(D)=\sum_{j\in D}d(j,S)$; for $c\in S$, $C^S_c$ is the cluster of $c$ in $S$. A center $o\in O$ is *synced* if some $c\in S$ has $|C_o\,\triangle\,C^S_c|\le\varepsilon\min(|C_o|,|C^S_c|)$, and *close* if it is not synced and $d(o,S)\le\tfrac{89}{100}\,\mathrm{avg}_O(o)+2\varepsilon\,\mathrm{avg}_S(o)$; $O_1\subseteq O$ is the set of centers that are neither.
--
--   **Good outcomes of the client sampling.** A list $\Lambda_1$ of dummies (pairs $(\ell,r)$ of a leader and a radius) is a *good outcome* if there are sets $O_\Lambda^{e}\subseteq O_\Lambda\subseteq O_1$ and an injective map $\varphi$ from $O_\Lambda$ to the entries of $\Lambda_1$, with $|\Lambda_1|=|O_\Lambda|$, such that:
--
--   1. for every $o\in O_\Lambda$ with $\varphi(o)=(\ell,r)$: $\ell$ is a client of $\mathrm{core}_{\kappa(o)}(o)$, and of $\mathrm{core}_{6\varepsilon}(o)$ if $o\in O_\Lambda^{e}$, and
--   $$d(o,\ell)\ \le\ r\ \le\ \bigl(1+\kappa(o)\,\mathbf 1[o\notin O_\Lambda^{e}]+8\varepsilon\bigr)\,\mathrm{per}(o)+\varepsilon\,\mathrm{avg}_S(o);$$
--   2. $\sum_{o\in O_1\setminus O_\Lambda^{e}}\mathrm{cost}_S\bigl(\mathrm{core}_{6\varepsilon}(o)\bigr)<\varepsilon^5\,\mathrm{opt}$ and $\sum_{o\in O_1\setminus O_\Lambda}\mathrm{cost}_S\bigl(\mathrm{core}_{\kappa(o)}(o)\bigr)<\varepsilon^5\,\mathrm{opt}$.
--
--   **The client sampling.** Let $LS$ be a list of distinct facility indices (each less than $m$) whose set is $S$. The sampling reads a vector $u\in\{0,\dots,2^b-1\}^{6s}$ of chunks and makes $2s$ iterations, starting from the empty list. Iteration $i$ reads $u_{3i},u_{3i+1},u_{3i+2}$: it draws the client $\ell$ with weights $d(j,S)$, namely the least $\ell$ with $2^b\sum_{j\le\ell}d(j,S)>u_{3i}\sum_{j}d(j,S)$ (client $0$ if there is none); if $2u_{3i+1}<2^b$ it does nothing; otherwise it appends the dummy with leader $\ell$ and radius $d(\ell,S)\,N^{-3}\bigl(\tfrac{N+1}{N}\bigr)^{x}$, $x=u_{3i+2}\bmod(10N^2+1)$.
--
--   **Statement.** With $q_1=1/(440N^8)$,
--   $$\#\bigl\{u\in\{0,\dots,2^b-1\}^{6s}:\ \text{the client sampling on }u\text{ returns a good outcome}\bigr\}\ \ge\ q_1^{\,2s}\,\bigl(2^b\bigr)^{6s}.$$
--
--   This is the first of the three factors in the probability that a trial of the algorithm is good; it is combined with the process lemma of the cluster sampling and with the color coding to show that a trial succeeds with probability at least $N^{-200s}$, which gives Theorem 1.1 after $N^{200s+1}$ repetitions.
--
--   **Formalization Note** The statement counts chunk vectors; dividing by $(2^b)^{6s}$ gives the probability over uniform chunks, each chunk being $b$ coin flips. Distances and radii are rational and computed exactly; the paper reads the skip coin after sampling the client, which makes no difference for independent chunks.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), Section 4.2 (client-sampling theorem, Algorithm 1) and Section 4.6. Lean source: `BCFGJPSSV26.Stable.Hyp.card_clientWitness`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Alg/ClientSampling.lean#L1215-L1252

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Coins
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Mixed
public import Definitions.Def_BCFGJPSSV26_Stable_Structure_ClientWitness
public import Definitions.Def_BCFGJPSSV26_Stable_Stability_FewNotInSync
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_ThreeApprox
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClientSampling

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace ClientSampling

section Analysis

variable (X : Ctx)

variable {X}

section Hyp

variable (H : Hyp X)
include H

end Hyp

end Analysis

section Radius

variable {X : Ctx}

section Hyp

variable (H : Hyp X)
include H

end Hyp

end Radius

section Iteration

variable {X : Ctx} {LS : List ℕ}

variable (X LS)

variable {X LS}

section Hyp

variable (H : Hyp X)
include H

end Hyp

end Iteration

section Density

variable {X : Ctx} {LS : List ℕ}

end Density

section Triples

end Triples

end ClientSampling

open ClientSampling in
open Classical in

theorem Hyp.card_clientWitness {X : Ctx} (H : Hyp X) {LS : List ℕ} (hLS : X.I.centers LS = X.S)
    (hLSnd : LS.Nodup) (hLSm : ∀ i ∈ LS, i < X.I.m) :
    X.P.q₁ ^ (2 * X.s) * ((2 : ℝ) ^ X.b) ^ (6 * X.s) ≤
      (univ.filter fun u : Fin (6 * X.s) → Fin (2 ^ X.b) ↦
        Nonempty (ClientWitness X
          (toDums X.I (csRun X.P.N (toRaw X.I) LS X.s X.b (toCh u))))).card := by sorry

end BCFGJPSSV26.Stable
end
