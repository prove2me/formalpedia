-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_Hyp_card_S_sdiff_LSX_le
-- name    : BCFGJPSSV26.Stable.Hyp.card_S_sdiff_LSX_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:49:23.269226+00:00
-- url     : https://prove2.me/theorems/ecba3cae-efdc-4055-abf5-39fee24d01f0
-- title:
--   At most $s=632NL$ local-search centers lie outside the substitute set $LS_X$
-- statement:
--   This lemma of the analysis of the cluster sampling (Part II, Section 4) says that the set $LS_X$ of substitutes known after the client sampling contains all but at most $s=632\,N\,L$ centers of the local-search solution.
--
--   **Standing hypotheses (H).** $I$ is a valid $k$-median instance ($n$ clients, $m$ facilities, rational pseudometric $d$) with $2\le k\le m$ and $\mathrm{opt}:=\mathrm{opt}_k>0$, where $\mathrm{opt}_\ell$ is the least cost of a nonempty set of at most $\ell$ facilities and $\mathrm{cost}(F)=\sum_j d(j,F)$. $N\ge 201$ is an integer and $\varepsilon=1/N$. $\beta>0$ is a real number, $I$ is $\beta$-stable, i.e. $\mathrm{opt}_{k-1}\ge(1+\beta)\,\mathrm{opt}_k$, and $L$ is a natural number with $L\ge 1/\beta$. $O$ is a set of exactly $k$ facilities with $\mathrm{cost}(O)=\mathrm{opt}$. $S$ is an approximate local optimum: $|S|=k$, and every nonempty set $T$ of at most $k$ facilities with $|S\setminus T|\le 24N$ satisfies $\mathrm{cost}(T)\ge\bigl(1-\tfrac{1}{Nk}\bigr)\mathrm{cost}(S)$.
--
--   For $c^\ast\in O$, $C^\ast$ denotes its optimal cluster (the clients whose nearest center of $O$ is $c^\ast$, ties going to the center of least index) and $\mathrm{cost}_{OPT}(C^\ast)=\sum_{j\in C^\ast}d(j,c^\ast)$. For $c\in S$, $C_c$ is the cluster of $c$ in $S$, defined in the same way, and $\mathrm{cost}_S(D)=\sum_{j\in D}d(j,S)$ for a set $D$ of clients. $\mathrm{per}(C^\ast)$ is the $\varepsilon$-percentile of $C^\ast$: the least value $t=d(j,c^\ast)$, $j\in C^\ast$, such that at least $\varepsilon|C^\ast|$ clients of $C^\ast$ are within distance $t$ of $c^\ast$. $\mathrm{avg}_{OPT}(C^\ast)=\mathrm{cost}_{OPT}(C^\ast)/|C^\ast|$ and $\mathrm{avg}_S(C^\ast)=\mathrm{cost}_S(C^\ast)/|C^\ast|$. With $\eta=89/100$, $x=\mathrm{per}(C^\ast)/\mathrm{avg}_{OPT}(C^\ast)$ ($x=1$ if $\mathrm{avg}_{OPT}(C^\ast)=0$) and $t=\max(\eta,\min(1,x))$, the parameter $\kappa=\kappa(C^\ast)$ is defined by $1+\kappa=(89-12t)/(65t)$. For $\gamma\ge 0$, $\mathrm{core}_\gamma(C^\ast)=\{j\in C^\ast: d(j,c^\ast)\le(1+\gamma)\,\mathrm{per}(C^\ast)\}$.
--
--   A center $c^\ast\in O$ is *synced* if some $c\in S$ satisfies $|C^\ast\,\triangle\,C_c|\le\varepsilon\,\min(|C^\ast|,|C_c|)$; $\sigma_{sync}(c^\ast)$ is one such $c$, chosen once and for all. A center $c^\ast\in O$ is *close* if it is not synced and $d(c^\ast,S)\le\eta\,\mathrm{avg}_{OPT}(C^\ast)+2\varepsilon\,\mathrm{avg}_S(C^\ast)$; $\sigma_{cl}(c^\ast)$ is the center of $S$ nearest to $c^\ast$ (of least index among the nearest ones). $O_{sync}$ and $O_{cl}$ are the sets of synced and of close centers. Put $O_{S0}=O_{sync}\cup O_{cl}$, $O_1=O\setminus O_{S0}$, and let $\sigma_0$ be $\sigma_{sync}$ on synced centers and $\sigma_{cl}$ on all others.
--
--   A *dummy* $\lambda=(\ell,r)$ is a point $\ell$ (its leader, a client or a facility) with a real radius $r$; its distance to a point $a$ is $d(a,\lambda)=d(a,\ell)+r$, and its *ball* is the set of facilities within distance $r$ of $\ell$.
--
--   **Good outcome of the client sampling** (the client-sampling theorem of Part II, Section 4.2). A list $\Lambda_1$ of dummies with sets $O_\Lambda^e\subseteq O_{\Lambda 1}\subseteq O_1$ (the hit clusters and, among them, the early ones) and an injective map $\varphi_1$ from $O_{\Lambda1}$ to the entries of $\Lambda_1$, where $|\Lambda_1|=|O_{\Lambda1}|$, such that for every $c^\ast\in O_{\Lambda1}$ with $\varphi_1(c^\ast)=(\ell,r)$:
--
--   - $\ell$ is a client of $\mathrm{core}_\kappa(C^\ast)$, and a client of $\mathrm{core}_{6\varepsilon}(C^\ast)$ if $c^\ast\in O_\Lambda^e$;
--   - $d(c^\ast,\ell)\le r\le\bigl(1+\kappa\,\mathbf 1[c^\ast\notin O_\Lambda^e]+8\varepsilon\bigr)\mathrm{per}(C^\ast)+\varepsilon\,\mathrm{avg}_S(C^\ast)$;
--
--   and such that $\sum_{c^\ast\in O_1\setminus O_\Lambda^e}\mathrm{cost}_S(\mathrm{core}_{6\varepsilon}(C^\ast))<\varepsilon^5\,\mathrm{opt}$ and $\sum_{c^\ast\in O_1\setminus O_{\Lambda1}}\mathrm{cost}_S(\mathrm{core}_{\kappa}(C^\ast))<\varepsilon^5\,\mathrm{opt}$.
--
--   **Statement.** Let $\Lambda_1$ be a good outcome of the client sampling, with hit clusters $O_{\Lambda1}$, and let
--
--   $$O_{S1}=\{c^\ast\in O_1\setminus O_{\Lambda1}:\ \mathrm{cost}_S(\mathrm{core}_\kappa(C^\ast))\ge\varepsilon^3\,\mathrm{cost}_{OPT}(C^\ast)\},\qquad LS_X=\sigma_0(O_{S0})\cup\sigma_{cl}(O_{S1}).$$
--
--   Then, with $s=632\,N\,L$,
--
--   $$|S\setminus LS_X|\;\le\;s .$$
--
--   In the analysis of the cluster sampling (Algorithm 2), a run that keeps the invariant deletes only centers of $S\setminus LS_X$. So it deletes at most $s$ centers, and its outcome $LS'$, with $LS_X\subseteq LS'\subseteq S$, satisfies $|S\setminus LS'|\le s$, one of the conditions of a good outcome of the cluster sampling used in the structural theorem (Theorems 3.1 and 3.2).
--
--   **Formalization Note** Of the outcome of the client sampling, only the set $O_{\Lambda1}$ enters the statement.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172). Lean source: `BCFGJPSSV26.Stable.Hyp.card_S_sdiff_LSX_le`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Structure/ClusterWitness.lean#L139-L150

module

public import Definitions.Def_BCFGJPSSV26_Stable_Structure_ClientWitness
public import Definitions.Def_BCFGJPSSV26_Stable_Stability_FewNotInSync
public import Definitions.Def_BCFGJPSSV26_Stable_Stability_SyncSub
public import Definitions.Def_BCFGJPSSV26_Stable_Structure_ClusterWitness

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace Ctx

variable (X : Ctx)

end Ctx

namespace Hyp

variable {X : Ctx} (H : Hyp X)
include H

theorem card_S_sdiff_LSX_le {Λ₁ : List (Dummy X.I)} (w₁ : ClientWitness X Λ₁) :
    (X.S \ X.LSX w₁.OL).card ≤ X.s := by sorry

end Hyp
end BCFGJPSSV26.Stable
end
