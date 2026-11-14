-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_Hyp_card_clusterWitness
-- name    : BCFGJPSSV26.Stable.Hyp.card_clusterWitness
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:44:54.302818+00:00
-- url     : https://prove2.me/theorems/30eb4b1f-efb3-48e2-9825-acacbaf4f0e6
-- title:
--   Cluster sampling (Part II, Section 4.4, Algorithm 2) — good outcomes have density at least $q_2^{20s+20}$
-- statement:
--   This is the process lemma of the cluster sampling: the cluster-sampling theorem of Part II (arXiv:2610.17172), Section 4.4, for Algorithm 2, as a lower bound on the number of random inputs for which the sampling, started from a good outcome of the client sampling, returns a good outcome.
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
--   **Notation (Part II, Section 4).** For $o\in O$, the *satellites* $\Gamma(o)$ are the $c\in S$ with $d(c,o)\le(1+\kappa(o)+2\varepsilon)\,\mathrm{per}(o)$ and $d(j,c)\le\varepsilon\,\mathrm{per}(o)$ for some $j\in C_o$; the *loose satellites* $\Gamma_\varepsilon(o)$ are defined with $3\varepsilon$ and $2\varepsilon$ in place of $2\varepsilon$ and $\varepsilon$; $\Gamma(A)=\bigcup_{o\in A}\Gamma(o)$. Given the hit clusters $O_\Lambda\subseteq O_1$ of the client sampling: $O_{S1}$ is the set of $o\in O_1\setminus O_\Lambda$ with $\mathrm{cost}_S(\mathrm{core}_{\kappa(o)}(o))\ge\varepsilon^3\,\mathrm{cost}_O(o)$, and $O_2=(O_1\setminus O_\Lambda)\setminus O_{S1}$; $LS_X\subseteq S$ consists of the substitutes of the synced centers (a sync partner) and of the close centers and the centers of $O_{S1}$ (the nearest center of $S$); $O_X$ is the set of $o\in O_2$ with $d(o,c)\le(1+\kappa(o)+4\varepsilon)\,\mathrm{per}(o)$ for some $c\in LS_X$; and $\mathcal O=O_2\setminus O_X$. A *mixed set* $M=(F,\Lambda)$ is a set $F$ of facilities with a list $\Lambda$ of dummies; $d(a,M)=\min\bigl(d(a,F),\min_{(\ell,r)\in\Lambda}(d(a,\ell)+r)\bigr)$, the cluster $M_c$ of $c\in F$ consists of the clients of the cluster of $c$ in $F$ that are not strictly nearer to a dummy, and $\mathrm{cost}_M(D)=\sum_{j\in D}d(j,M)$.
--
--   **Good outcomes of the cluster sampling.** Let $\Lambda_1$ be a good outcome of the client sampling, with hit clusters $O_\Lambda$. A pair $(LS',\Lambda_2)$ of a set of facilities and a list of dummies is a *good outcome* if there are a set $O_{\Lambda2}\subseteq O_2\setminus O_X$ and an injective map $\varphi_2$ from $O_{\Lambda2}$ to the entries of $\Lambda_2$, with $|\Lambda_2|=|O_{\Lambda2}|$, such that, with $O_B=(O_2\setminus O_X)\setminus O_{\Lambda2}$ and $M=(LS',\Lambda_1\cup\Lambda_2)$:
--
--   1. $LS_X\subseteq LS'\subseteq S$ and $|S\setminus LS'|\le s$;
--   2. for $o\in O_{\Lambda2}$ with $\varphi_2(o)=(\ell,r)$: $\ell$ is a facility of $S$ and $d(o,\ell)\le r\le(1+\kappa(o)+6\varepsilon)\,\mathrm{per}(o)$;
--   3. $\Gamma(O_B)\subseteq LS'$;
--   4. $\sum_{c\in\Gamma(O_B)}\mathrm{cost}_S(C^S_c)<\varepsilon^3\mathrm{opt}$ and $\sum_{c\in\Gamma(O_B)\cup(LS'\setminus LS_X)}\mathrm{cost}_M(M_c)<\varepsilon^3\mathrm{opt}$.
--
--   **The cluster sampling.** Let $LS$ be a list of distinct facility indices whose set is $S$. Started from $\Lambda_1$, the sampling makes $20s+20$ steps of a state machine, each reading one chunk of $u\in\{0,\dots,2^b-1\}^{20s+20}$: in two phases of $s$ iterations it samples centers of $S$ (by their local-search cluster cost, resp. by the cost of their cluster in the current mixed set), deletes centers, and adds dummies led by centers of $S$ with radii on a geometric grid. It returns the kept centers $LS'$ and the list $\Lambda_2$ of new dummies.
--
--   **Statement.** Let $\Lambda_1$ be a list of dummies whose leaders are points of $I$ and whose radii are rational, and fix a certificate $(O_\Lambda,O_\Lambda^e,\varphi)$ that $\Lambda_1$ is a good outcome of the client sampling. With $q_2=1/(12N^3)$,
--   $$\#\bigl\{u\in\{0,\dots,2^b-1\}^{20s+20}:\ \text{the cluster sampling on }u\text{ returns a good outcome}\bigr\}\ \ge\ q_2^{\,20s+20}\,\bigl(2^b\bigr)^{20s+20}.$$
--
--   This is the second factor in the probability that a trial is good: together with the process lemma of the client sampling and the color coding it shows that a trial succeeds with probability at least $N^{-200s}$. Good outcomes of both samplings are the input of the structural theorem (Theorems 3.1 and 3.2).
--
--   **Formalization Note** The statement counts chunk vectors of $b$ coin flips per chunk. Good outcomes of the cluster sampling are relative to the chosen certificate of the client sampling, through $O_\Lambda$. The sync partner of a synced center is a fixed choice.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), Section 4.4 (cluster-sampling theorem, Algorithm 2), proof in Section 4.7. Lean source: `BCFGJPSSV26.Stable.Hyp.card_clusterWitness`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Alg/ClusterSamplingAnalysis.lean#L113-L137

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSampling
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingDensity
public import Definitions.Def_BCFGJPSSV26_Stable_Structure_ClusterWitness
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingAnalysis

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace KSData

variable (K : KSData)

end KSData

open Classical in

theorem Hyp.card_clusterWitness {X : Ctx} (H : Hyp X) {LS : List ℕ}
    (hLS : X.I.centers LS = X.S) (hLSnd : LS.Nodup) (hLSm : ∀ i ∈ LS, i < X.I.m)
    {Λ₁ : List DumQ} (hΛ₁ : (toRaw X.I).ValidDums Λ₁) (w₁ : ClientWitness X (toDums X.I Λ₁)) :
    X.P.q₂ ^ Par.M₂ X.P.N X.L * ((2 : ℝ) ^ X.b) ^ Par.M₂ X.P.N X.L ≤
      (univ.filter fun u : Fin (Par.M₂ X.P.N X.L) → Fin (2 ^ X.b) ↦
        Nonempty (ClusterWitness w₁
          (X.I.centers (ksLS' LS (ksRun X.P.N (toRaw X.I) LS Λ₁ X.s X.b (toCh u))))
          (toDums X.I (ksRun X.P.N (toRaw X.I) LS Λ₁ X.s X.b (toCh u)).dums))).card := by sorry

end BCFGJPSSV26.Stable
end
