-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_Hyp_exists_partition
-- name    : BCFGJPSSV26.Stable.Hyp.exists_partition
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:49:39.704514+00:00
-- url     : https://prove2.me/theorems/b0355f27-f57e-4dc3-8abd-0ba27d558ddf
-- title:
--   Theorems 3.1 and 3.2 (Part II) — the structural theorem: good sampling outcomes give a partition of $O$
-- statement:
--   This is the structural theorem of Part II (Theorems 3.1 and 3.2): from good outcomes of the client sampling and of the cluster sampling, the optimal centers split into centers with substitutes, with dummies, with backups and with satellites, with the cost and size bounds listed below.
--
--   **Standing hypotheses (H).** $I$ is a valid $k$-median instance ($n$ clients, $m$ facilities, rational pseudometric $d$) with $2\le k\le m$ and $\mathrm{opt}:=\mathrm{opt}_k>0$, where $\mathrm{opt}_\ell$ is the least cost of a nonempty set of at most $\ell$ facilities and $\mathrm{cost}(F)=\sum_j d(j,F)$. $N\ge 201$ is an integer and $\varepsilon=1/N$. $\beta>0$ is a real number, $I$ is $\beta$-stable, i.e. $\mathrm{opt}_{k-1}\ge(1+\beta)\,\mathrm{opt}_k$, and $L$ is a natural number with $L\ge 1/\beta$. $O$ is a set of exactly $k$ facilities with $\mathrm{cost}(O)=\mathrm{opt}$. $S$ is an approximate local optimum: $|S|=k$, and every nonempty set $T$ of at most $k$ facilities with $|S\setminus T|\le 24N$ satisfies $\mathrm{cost}(T)\ge\bigl(1-\tfrac{1}{Nk}\bigr)\mathrm{cost}(S)$.
--
--   For $c^\ast\in O$, $C^\ast$ denotes its optimal cluster (the clients whose nearest center of $O$ is $c^\ast$, ties going to the center of least index) and $\mathrm{cost}_{OPT}(C^\ast)=\sum_{j\in C^\ast}d(j,c^\ast)$. For $c\in S$, $C_c$ is the cluster of $c$ in $S$, defined in the same way, and $\mathrm{cost}_S(D)=\sum_{j\in D}d(j,S)$ for a set $D$ of clients. $\mathrm{per}(C^\ast)$ is the $\varepsilon$-percentile of $C^\ast$: the least value $t=d(j,c^\ast)$, $j\in C^\ast$, such that at least $\varepsilon|C^\ast|$ clients of $C^\ast$ are within distance $t$ of $c^\ast$. $\mathrm{avg}_{OPT}(C^\ast)=\mathrm{cost}_{OPT}(C^\ast)/|C^\ast|$ and $\mathrm{avg}_S(C^\ast)=\mathrm{cost}_S(C^\ast)/|C^\ast|$. With $\eta=89/100$, $x=\mathrm{per}(C^\ast)/\mathrm{avg}_{OPT}(C^\ast)$ ($x=1$ if $\mathrm{avg}_{OPT}(C^\ast)=0$) and $t=\max(\eta,\min(1,x))$, the parameter $\kappa=\kappa(C^\ast)$ is defined by $1+\kappa=(89-12t)/(65t)$. For $\gamma\ge 0$, $\mathrm{core}_\gamma(C^\ast)=\{j\in C^\ast: d(j,c^\ast)\le(1+\gamma)\,\mathrm{per}(C^\ast)\}$.
--
--   A center $c^\ast\in O$ is *synced* if some $c\in S$ satisfies $|C^\ast\,\triangle\,C_c|\le\varepsilon\,\min(|C^\ast|,|C_c|)$; $\sigma_{sync}(c^\ast)$ is one such $c$, chosen once and for all. A center $c^\ast\in O$ is *close* if it is not synced and $d(c^\ast,S)\le\eta\,\mathrm{avg}_{OPT}(C^\ast)+2\varepsilon\,\mathrm{avg}_S(C^\ast)$; $\sigma_{cl}(c^\ast)$ is the center of $S$ nearest to $c^\ast$ (of least index among the nearest ones). $O_{sync}$ and $O_{cl}$ are the sets of synced and of close centers. Put $O_{S0}=O_{sync}\cup O_{cl}$, $O_1=O\setminus O_{S0}$, and let $\sigma_0$ be $\sigma_{sync}$ on synced centers and $\sigma_{cl}$ on all others.
--
--   A *dummy* $\lambda=(\ell,r)$ is a point $\ell$ (its leader, a client or a facility) with a real radius $r$; its distance to a point $a$ is $d(a,\lambda)=d(a,\ell)+r$, and its *ball* is the set of facilities within distance $r$ of $\ell$. For a set $F$ of facilities and a list $\Lambda$ of dummies, the *mixed set* $(F,\Lambda)$ has $d(a,(F,\Lambda))=\min\bigl(d(a,F),\min_{\lambda\in\Lambda}d(a,\lambda)\bigr)$ and $\mathrm{cost}(F,\Lambda)=\sum_j d(j,(F,\Lambda))$. The cluster $M_c$ of a facility $c\in F$ in $(F,\Lambda)$ consists of the clients whose nearest facility of $F$ is $c$ (ties to the least index) and that are at least as near to $F$ as to every dummy; $\mathrm{cost}_{(F,\Lambda)}(E)=\sum_{j\in E}d(j,(F,\Lambda))$.
--
--   **Good outcome of the client sampling** (the client-sampling theorem of Part II, Section 4.2). A list $\Lambda_1$ of dummies with sets $O_\Lambda^e\subseteq O_{\Lambda 1}\subseteq O_1$ (the hit clusters and, among them, the early ones) and an injective map $\varphi_1$ from $O_{\Lambda1}$ to the entries of $\Lambda_1$, where $|\Lambda_1|=|O_{\Lambda1}|$, such that for every $c^\ast\in O_{\Lambda1}$ with $\varphi_1(c^\ast)=(\ell,r)$:
--
--   - $\ell$ is a client of $\mathrm{core}_\kappa(C^\ast)$, and a client of $\mathrm{core}_{6\varepsilon}(C^\ast)$ if $c^\ast\in O_\Lambda^e$;
--   - $d(c^\ast,\ell)\le r\le\bigl(1+\kappa\,\mathbf 1[c^\ast\notin O_\Lambda^e]+8\varepsilon\bigr)\mathrm{per}(C^\ast)+\varepsilon\,\mathrm{avg}_S(C^\ast)$;
--
--   and such that $\sum_{c^\ast\in O_1\setminus O_\Lambda^e}\mathrm{cost}_S(\mathrm{core}_{6\varepsilon}(C^\ast))<\varepsilon^5\,\mathrm{opt}$ and $\sum_{c^\ast\in O_1\setminus O_{\Lambda1}}\mathrm{cost}_S(\mathrm{core}_{\kappa}(C^\ast))<\varepsilon^5\,\mathrm{opt}$.
--
--   Given such an outcome, put $O_{S1}=\{c^\ast\in O_1\setminus O_{\Lambda1}:\ \mathrm{cost}_S(\mathrm{core}_\kappa(C^\ast))\ge\varepsilon^3\,\mathrm{cost}_{OPT}(C^\ast)\}$, $O_2=(O_1\setminus O_{\Lambda1})\setminus O_{S1}$, $LS_X=\sigma_0(O_{S0})\cup\sigma_{cl}(O_{S1})$ and $O_X=\{c^\ast\in O_2:\ d(c^\ast,c)\le(1+\kappa+4\varepsilon)\,\mathrm{per}(C^\ast)\text{ for some }c\in LS_X\}$. The *satellites* of $c^\ast$ are $\Gamma(c^\ast)=\{c\in S:\ d(c,c^\ast)\le(1+\kappa+2\varepsilon)\,\mathrm{per}(C^\ast)\text{ and } d(j,c)\le\varepsilon\,\mathrm{per}(C^\ast)\text{ for some }j\in C^\ast\}$, and $\Gamma(A)=\bigcup_{c^\ast\in A}\Gamma(c^\ast)$.
--
--   **Good outcome of the cluster sampling** (Part II, Section 4.4). A set $LS'$ of facilities and a list $\Lambda_2$ of dummies with a set $O_{\Lambda2}\subseteq O_2\setminus O_X$ and an injective map $\varphi_2$ from $O_{\Lambda2}$ to the entries of $\Lambda_2$, where $|\Lambda_2|=|O_{\Lambda2}|$, such that, with $O_B=(O_2\setminus O_X)\setminus O_{\Lambda2}$, $s=632NL$ and $M'=(LS',\Lambda_1\Lambda_2)$:
--
--   - $LS_X\subseteq LS'\subseteq S$ and $|S\setminus LS'|\le s$;
--   - for $c^\ast\in O_{\Lambda2}$ with $\varphi_2(c^\ast)=(\ell,r)$: $\ell$ is a facility of $S$ and $d(c^\ast,\ell)\le r\le(1+\kappa+6\varepsilon)\,\mathrm{per}(C^\ast)$;
--   - $\Gamma(O_B)\subseteq LS'$;
--   - $\sum_{c\in\Gamma(O_B)}\mathrm{cost}_S(C_c)<\varepsilon^3\mathrm{opt}$ and $\sum_{c\in\Gamma(O_B)\cup(LS'\setminus LS_X)}\mathrm{cost}_{M'}(M_c)<\varepsilon^3\mathrm{opt}$.
--
--   **Statement.** For good outcomes $\Lambda_1$ and $(LS',\Lambda_2)$, there exist sets $O_P,O_R$ of facilities, maps $\psi,\sigma$ from facilities to facilities and a set $Z^\ast$ of facilities such that, with $O_S=O_{S0}\cup O_{S1}$, $O_\Lambda=O_{\Lambda1}\cup O_{\Lambda2}$ and $LS_\sigma=\sigma_0(O_S)\cup\sigma(O_R)$:
--
--   1. $O_P\cup O_R=O_X\cup O_B$, $O_P\cap O_R=\emptyset$ and $O_X\subseteq O_P$ (so $O$ is the disjoint union of $O_S$, $O_\Lambda$, $O_P$, $O_R$);
--   2. $|O_{\Lambda1}|+|O_{\Lambda2}|+|O_P|+|O_R|\le s$;
--   3. for $c^\ast\in O_P$: $\psi(c^\ast)\in LS_\sigma$, $d(c^\ast,\psi(c^\ast))\le(1+\kappa+4\varepsilon)\,\mathrm{per}(C^\ast)$ and $\mathrm{per}(C^\ast)>0$;
--   4. for $c^\ast\in O_R$: $\sigma(c^\ast)\in\Gamma(c^\ast)$, $d(c^\ast,\sigma(c^\ast))\le(1+\varepsilon)\,\mathrm{per}(C^\ast)$ and $\sigma(c^\ast)\notin\sigma_0(O_S)$; and $\sigma$ is injective on $O_R$;
--   5. $\sigma_0(O_S)\subseteq LS'$ and $\Gamma(O_R)\subseteq LS'$;
--   6. $\sum_{c^\ast\in O_S}\sum_{j\in C^\ast}d(j,\sigma_0(c^\ast))\le(1+\eta)\sum_{c^\ast\in O_S}\mathrm{cost}_{OPT}(C^\ast)+30\,\varepsilon\,\mathrm{opt}$;
--   7. $\sum_{c\in\Gamma(O_R)\cup(LS'\setminus LS_\sigma)}\mathrm{cost}_{M'}(M_c)<\varepsilon^3\mathrm{opt}$ and $\sum_{c\in\Gamma(O_R)}\mathrm{cost}_S(C_c)<\varepsilon^3\mathrm{opt}$;
--   8. $\sum_{c^\ast\in O_P\cup(O_\Lambda\setminus O_\Lambda^e)}\mathrm{cost}_S(\mathrm{core}_{6\varepsilon}(C^\ast))<\varepsilon^5\mathrm{opt}$ and $\sum_{c^\ast\in O_R}\mathrm{cost}_S(\mathrm{core}_\kappa(C^\ast))<\varepsilon^5\mathrm{opt}$;
--   9. every $c^\ast\in O_R$ is *far*: $c^\ast\in O$; $\eta\,\mathrm{avg}_{OPT}(C^\ast)+2\varepsilon\,\mathrm{avg}_S(C^\ast)<d(c^\ast,S)$; $\mathrm{cost}_S(\mathrm{core}_\kappa(C^\ast))<\varepsilon^3\mathrm{cost}_{OPT}(C^\ast)$; $\mathrm{per}(C^\ast)/(1+2\varepsilon)\le\mathrm{avg}_{OPT}(C^\ast)\le(1+\varepsilon)\,\mathrm{per}(C^\ast)/\eta$; $\mathrm{cost}_{OPT}(C^\ast)>0$ and $\mathrm{per}(C^\ast)>0$; and some $c\in\Gamma(c^\ast)$ has $d(c^\ast,c)\le(1+\varepsilon)\,\mathrm{per}(C^\ast)$ and $d(j,c)\le\varepsilon\,\mathrm{per}(C^\ast)$ for some $j\in C^\ast$;
--   10. $Z^\ast\subseteq LS'\setminus LS_\sigma$ and $|Z^\ast|=\max\bigl(0,\ |LS'|+|\Lambda_1|+|\Lambda_2|+|O_P|-k\bigr)$.
--
--   The partition is the interface between the sampling part of the algorithm and its two cost bounds: the nuanced local-search bound (Theorem 3.8) and the bound on the submodular candidate (Theorem 3.4) are both sums of rows over the four classes, and $Z^\ast$ is the set of centers that the color coding has to guess for closing.
--
--   **Formalization Note** The conclusion is the nonemptiness of a Lean structure with these fields.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), Theorems 3.1 and 3.2. Lean source: `BCFGJPSSV26.Stable.Hyp.exists_partition`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Structure/Partition.lean#L469-L605

module

public import Definitions.Def_BCFGJPSSV26_Stable_Structure_ClusterWitness
public import Definitions.Def_BCFGJPSSV26_Stable_Structure_Partition

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace Ctx

variable (X : Ctx)

end Ctx

variable {X : Ctx}

namespace Partition

variable {X : Ctx} {Λ₁ : List (Dummy X.I)} {w₁ : ClientWitness X Λ₁}
  {LS' : Finset (Fin X.I.m)} {Λ₂ : List (Dummy X.I)} {w₂ : ClusterWitness w₁ LS' Λ₂}
  (Q : Partition w₂)

end Partition

theorem Hyp.exists_partition {X : Ctx} (H : Hyp X) {Λ₁ : List (Dummy X.I)}
    (w₁ : ClientWitness X Λ₁) {LS' : Finset (Fin X.I.m)} {Λ₂ : List (Dummy X.I)}
    (w₂ : ClusterWitness w₁ LS' Λ₂) : Nonempty (Partition w₂) := by sorry

end BCFGJPSSV26.Stable
end
