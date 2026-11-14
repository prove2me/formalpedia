-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_KSData_Base_sum_wt_le
-- name    : BCFGJPSSV26.Stable.KSData.Base.sum_wt_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:46:55.668487+00:00
-- url     : https://prove2.me/theorems/703ee370-0be0-4671-96aa-ff66b1638aab
-- title:
--   Cluster-sampling invariant — the total sampling weight is at most $6\,\mathrm{opt}$
-- statement:
--   A bound of the analysis of the cluster sampling (Part II, arXiv:2610.17172, Section 4.7, from the claim on the intermediate cost): in both phases, the weights with which the sampling draws a kept center add up to at most $6\,\mathrm{opt}$.
--
--   **Setting.** The standing hypotheses of Part II, Sections 3–6, hold: $N\ge201$ is an integer and $\varepsilon=1/N$; $I$ is a valid $k$-median instance with $2\le k\le m$ and $\mathrm{opt}:=\mathrm{opt}_k>0$, $\beta$-stable for some $\beta>0$ ($\mathrm{opt}_{k-1}\ge(1+\beta)\mathrm{opt}_k$); $L\ge1/\beta$ is a natural number, $s=632NL$, $b=|\mathrm{enc}(I)|+7N$; $O$ is an optimal set of exactly $k$ facilities; $S$ is an approximate local optimum ($|S|=k$, and no nonempty $T$ with $|T|\le k$ and $|S\setminus T|\le24N$ costs less than $(1-\frac{1}{Nk})\mathrm{cost}(S)$), given as a list $LS$ of distinct facility indices. A list $\Lambda_1$ of dummies (a point of $I$ with a rational radius) is fixed, together with a certificate that it is a good outcome of the client sampling in the sense of the client-sampling theorem of Part II, Section 4.2; $O_\Lambda\subseteq O_1$ denotes its set of hit clusters. For $o\in O$: $C_o$ is the optimal cluster of $o$, $\mathrm{cost}_O(o)=\sum_{j\in C_o}d(j,o)$, $\mathrm{per}(o)$ is the $\varepsilon$-percentile (the least distance $d(j,o)$, $j\in C_o$, within which at least $\varepsilon|C_o|$ clients of $C_o$ lie), $\mathrm{core}_\gamma(o)$ is the set of clients of $C_o$ within $(1+\gamma)\,\mathrm{per}(o)$ of $o$, and $\kappa(o)\in[\tfrac{12}{65},\tfrac{23}{65}]$ is the parameter of Part II, Lemma 3.9. For $c\in S$, $C^S_c$ is the cluster of $c$ in $S$, and $\mathrm{cost}_S(D)=\sum_{j\in D}d(j,S)$ for a set $D$ of clients. $O_1$ is the set of optimal centers that are neither synced nor close (Part II, Section 4.1).
--
--   **Notation (Part II, Section 4).** For $o\in O$, the *satellites* $\Gamma(o)$ are the $c\in S$ with $d(c,o)\le(1+\kappa(o)+2\varepsilon)\,\mathrm{per}(o)$ and $d(j,c)\le\varepsilon\,\mathrm{per}(o)$ for some $j\in C_o$; the *loose satellites* $\Gamma_\varepsilon(o)$ are defined with $3\varepsilon$ and $2\varepsilon$ in place of $2\varepsilon$ and $\varepsilon$; $\Gamma(A)=\bigcup_{o\in A}\Gamma(o)$. Given the hit clusters $O_\Lambda\subseteq O_1$ of the client sampling: $O_{S1}$ is the set of $o\in O_1\setminus O_\Lambda$ with $\mathrm{cost}_S(\mathrm{core}_{\kappa(o)}(o))\ge\varepsilon^3\,\mathrm{cost}_O(o)$, and $O_2=(O_1\setminus O_\Lambda)\setminus O_{S1}$; $LS_X\subseteq S$ consists of the substitutes of the synced centers (a sync partner) and of the close centers and the centers of $O_{S1}$ (the nearest center of $S$); $O_X$ is the set of $o\in O_2$ with $d(o,c)\le(1+\kappa(o)+4\varepsilon)\,\mathrm{per}(o)$ for some $c\in LS_X$; and $\mathcal O=O_2\setminus O_X$. A *mixed set* $M=(F,\Lambda)$ is a set $F$ of facilities with a list $\Lambda$ of dummies; $d(a,M)=\min\bigl(d(a,F),\min_{(\ell,r)\in\Lambda}(d(a,\ell)+r)\bigr)$, the cluster $M_c$ of $c\in F$ consists of the clients of the cluster of $c$ in $F$ that are not strictly nearer to a dummy, and $\mathrm{cost}_M(D)=\sum_{j\in D}d(j,M)$.
--
--   **Ghost matching and base clauses.** For a list $D$ of dummies, the dummies of $D$ are assigned, in order, to clusters of $\mathcal O$: each takes the cluster of least index not yet assigned of which its leader is a loose satellite, if there is one. $O_B(D)$ is the set of unassigned clusters of $\mathcal O$. A pair $(R^-,D)$, with $R^-$ a list of facility indices (the deleted centers) and $D$ a list of dummies, satisfies the *base clauses* if
--
--   1. $D$ and $R^-$ have no repeated entries;
--   2. the number of assigned clusters equals the length of $D$ (every dummy is assigned a cluster);
--   3. every assigned cluster $o$, with its dummy $(\ell,r)$, satisfies $d(o,\ell)\le r\le(1+\kappa(o)+6\varepsilon)\,\mathrm{per}(o)$;
--   4. every entry of $R^-$ is a center of $S\setminus LS_X$.
--
--   **Weights.** For a pair $(R^-,D)$ let $LS'=S\setminus R^-$ and $M=(LS',\Lambda_1\cup D)$. The weight of a center $c$ is $w_0(c)=\mathrm{cost}_S(C^S_c)$, the cost of its local-search cluster, in phase $0$, and $w_1(c)=\mathrm{cost}_M(M_c)$, the cost in $M$ of its cluster in $M$, in any other phase.
--
--   **Statement.** Suppose that $(R^-,D)$ satisfies the base clauses, that the leaders of the dummies of $D$ are points of $I$, and that no satellite of an unassigned cluster is deleted (no element of $\Gamma(O_B(D))$ is in $R^-$). Then, for $w=w_0$ and for $w=w_1$,
--   $$\sum_{c\in LS'}w(c)\ \le\ 6\,\mathrm{opt}.$$
--
--   The bound gives the density of the sampling step in the process lemma of the cluster sampling: when the cost condition of the phase fails, the good centers carry at least $\varepsilon^3\mathrm{opt}$ of a total weight of at most $6\,\mathrm{opt}$, so a weighted sample hits one of them with probability about $\varepsilon^3/6$.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), Section 4.7 (claim on the intermediate cost, in the proof of the cluster-sampling theorem). Lean source: `BCFGJPSSV26.Stable.KSData.Base.sum_wt_le`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Alg/ClusterSamplingBridge.lean#L391-L418

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingGhost
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingBridge

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace KSData

variable (K : KSData)

section

variable {K}

end

section

variable {K}

theorem Base.sum_wt_le {del : List ℕ} {D : List DumQ} (hb : K.Base del D)
    (hD : (toRaw K.X.I).ValidDums D) (hg : K.GamSub del D) (ph : ℕ) :
    ∑ c ∈ K.LSp del, K.wt ph del D c ≤ 6 * K.X.opt := by sorry

end
end KSData
end BCFGJPSSV26.Stable
end
