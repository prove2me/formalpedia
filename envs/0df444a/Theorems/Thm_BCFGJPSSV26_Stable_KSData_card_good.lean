-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_KSData_card_good
-- name    : BCFGJPSSV26.Stable.KSData.card_good
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:46:31.836376+00:00
-- url     : https://prove2.me/theorems/431920b3-f112-4963-8597-88ce84c3667f
-- title:
--   Cluster sampling — from every invariant state, at least a fraction $1/(12N^3)$ of the chunks is good
-- statement:
--   The density step of the analysis of the cluster sampling (Part II, arXiv:2610.17172, cluster-sampling theorem of Section 4.4, proof in Section 4.7): from every state of the sampling that satisfies the invariant of the analysis, a fixed fraction of the possible next chunks of coins is good.
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
--   **The cluster sampling** (Part II, Algorithm 2) is a state machine reading one chunk $u$ per step. A state consists of a phase $\phi$ ($0$, $1$, or $2$ when done), a counter $j$, the list $R^-$ of deleted centers, the list $\Lambda_2$ of dummies, and a mode with a current center $\ell$ and a radius base $r_0$. Write $LS'=LS\setminus R^-$, and "bit" for the fair bit $[\,2u<2^b\,]$. In phase $2$ a step changes nothing; otherwise:
--
--   - START: if $j=s$, pass to the next phase with $j=0$; else on bit $1$ end the iteration, on bit $0$ go to SAMPLE.
--   - SAMPLE: if $LS'=\emptyset$ end the iteration; else draw $\ell\in LS'$ by a weighted sample from $u$ and go to RADD. The weight of $c$ is $\mathrm{cost}_S(C^S_c)$ in phase $0$ and $\mathrm{cost}_M(M_c)$, $M=(LS',\Lambda_1\cup\Lambda_2)$, in phase $1$.
--   - RADD: if $|R^-|\le s$ and the bit is $1$, delete $\ell$ and end the iteration; else go to DG.
--   - DG: if $|\Lambda_2|+|R^-|>2s$ or no center other than $\ell$ is kept, end the iteration; else, with $c'$ the kept center other than $\ell$ nearest to $\ell$: on bit $1$ go to RG with $r_0=d(\ell,c')$, on bit $0$ delete $c'$.
--   - RG: if $|\Lambda_2|+|R^-|>2s$, delete $\ell$ and end the iteration; else append the dummy with leader $\ell$ and radius $r_0N^{-3}\bigl(\tfrac{N+1}{N}\bigr)^{x}+|\Lambda_2|\,r_0/(N^4(2s+2))$, $x=u\bmod(10N^2+1)$, and go to RGB.
--   - RGB: on bit $1$ delete $\ell$ and end the iteration; on bit $0$ go back to RG.
--
--   Ending an iteration means $j\leftarrow j+1$ and mode START. The initial state has $\phi=0$, $j=0$, empty lists and mode START.
--
--   **The invariant.** Write $O_B=O_B(\Lambda_2)$, and let $\mathrm{CC}_0$ be the condition $\sum_{c\in\Gamma(O_B)}\mathrm{cost}_S(C^S_c)<\varepsilon^3\mathrm{opt}$ and $\mathrm{CC}_1$ the condition $\sum_{c\in\Gamma(O_B)\cup(LS'\setminus LS_X)}\mathrm{cost}_M(M_c)<\varepsilon^3\mathrm{opt}$. The *good centers* are those of $\Gamma(O_B)$ in phase $0$, and of $\Gamma(O_B)\cup(LS'\setminus LS_X)$ otherwise. A state satisfies the invariant if:
--
--   1. $(R^-,\Lambda_2)$ satisfies the base clauses; $\phi\le2$; $j\le s$, and $j\lt s$ outside START;
--   2. every dummy of $\Lambda_2$ is led by a deleted center, or, in the modes RG and RGB, by the current center $\ell$ with radius $r_0N^{-3}(\tfrac{N+1}{N})^{x}+t\,r_0/(N^4(2s+2))$ for some $x<10N^2+1$ and $t<|\Lambda_2|$;
--   3. in the modes START, SAMPLE, RADD, no center of $\Gamma(O_B)$ is deleted;
--   4. $\mathrm{CC}_0$ holds if $\phi\ge1$; if $\phi=2$, $\mathrm{CC}_1$ holds and the mode is START;
--   5. if $\phi<2$: in START, $\mathrm{CC}_\phi$ holds or $j\le|R^-|$; outside START, $j\le|R^-|$; in SAMPLE, $\mathrm{CC}_\phi$ fails; in RADD, $\ell$ is a kept center of $LS$ and a good center;
--   6. if $\phi<2$, in DG, RG, RGB: $\ell$ is a kept center of $S\setminus LS_X$ and a loose satellite of every cluster of $O_B$ that has a deleted satellite; in DG, moreover, $\ell\in\Gamma(o_0)$ for some $o_0\in O_B$ that has a kept satellite $w$ with $\varepsilon\,\mathrm{per}(o_0)/2\le d(\ell,w)<5\,\mathrm{per}(o_0)$; in RG, $\ell\in\Gamma_\varepsilon(o)$ for some $o\in O_B$; in RG and RGB, $r_0>0$ and $\varepsilon^2\mathrm{per}(o)/3\le r_0\le15\,\mathrm{per}(o)$ for every $o\in O_B$ with $\ell\in\Gamma_\varepsilon(o)$.
--
--   **Good chunks.** A chunk $u$ is *good* for a state if: in phase $2$, always; in START, $j=s$ or (the bit is $1$ iff $\mathrm{CC}_\phi$ holds); in SAMPLE, the sampled center is a good center; in RADD, the bit is $1$ iff $\ell\notin\Gamma(O_B)$; in DG, the bit is $1$ iff some $o\in O_B$ has $\ell\in\Gamma_\varepsilon(o)$ and $\varepsilon^2\mathrm{per}(o)\le d(\ell,c')$, $c'$ being the nearest other kept center; in RG, if the ghost matching would assign a cluster $o$ to a new dummy led by $\ell$, then the grid radius $g=r_0N^{-3}(\tfrac{N+1}{N})^{u\bmod(10N^2+1)}$ satisfies $d(o,\ell)\le g\le(1+\varepsilon)\,d(o,\ell)$; in RGB, the bit is $1$ iff no $o\in O_B$ has $\ell\in\Gamma_\varepsilon(o)$.
--
--   **Statement.** If a state satisfies the invariant, then, with $q_2=1/(12N^3)$,
--   $$\#\bigl\{u\in\{0,\dots,2^b-1\}:\ u\text{ is good for the state}\bigr\}\ \ge\ q_2\cdot2^b .$$
--
--   Together with the fact that a good chunk preserves the invariant, this is the input of the guided-counting lemma, which yields the process lemma of the cluster sampling: at least $q_2^{20s+20}(2^b)^{20s+20}$ chunk vectors lead to a good outcome.
--
--   **Formalization Note** The cost conditions and the matched clusters are functions of the state through the ghost matching, which is not computed by the algorithm. A chunk is $b=|\mathrm{enc}(I)|+7N$ coin flips read as a number below $2^b$.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), Section 4.7 (proof of the cluster-sampling theorem of Section 4.4). Lean source: `BCFGJPSSV26.Stable.KSData.card_good`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Alg/ClusterSamplingDensity.lean#L287-L315

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingStep
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingDensity

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace KSData

variable (K : KSData)

open Classical in

theorem card_good {st : KSState} (hI : K.Inv st) :
    K.X.P.q₂ * (Fintype.card (Fin (2 ^ K.X.b)) : ℝ) ≤
      ((univ : Finset (Fin (2 ^ K.X.b))).filter fun u : Fin (2 ^ K.X.b) ↦ K.Good st u).card := by sorry

end KSData
end BCFGJPSSV26.Stable
end
