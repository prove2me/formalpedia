-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_Hyp_costMix_intermediate_lt
-- name    : BCFGJPSSV26.Stable.Hyp.costMix_intermediate_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:49:19.979821+00:00
-- url     : https://prove2.me/theorems/78904748-1f5a-4fdf-a876-9fdccc7bfac5
-- title:
--   Intermediate mixed sets of the cluster sampling cost less than $6\,\mathrm{opt}$ (Part II, Section 4.7)
-- statement:
--   This is the claim on the intermediate cost of Part II, Section 4.7: every mixed set of facilities and dummies that the cluster sampling can hold while it follows the analysis costs less than $6\,\mathrm{opt}$.
--
--   **Standing hypotheses (H).** $I$ is a valid $k$-median instance ($n$ clients, $m$ facilities, rational pseudometric $d$) with $2\le k\le m$ and $\mathrm{opt}:=\mathrm{opt}_k>0$, where $\mathrm{opt}_\ell$ is the least cost of a nonempty set of at most $\ell$ facilities and $\mathrm{cost}(F)=\sum_j d(j,F)$. $N\ge 201$ is an integer and $\varepsilon=1/N$. $\beta>0$ is a real number, $I$ is $\beta$-stable, i.e. $\mathrm{opt}_{k-1}\ge(1+\beta)\,\mathrm{opt}_k$, and $L$ is a natural number with $L\ge 1/\beta$. $O$ is a set of exactly $k$ facilities with $\mathrm{cost}(O)=\mathrm{opt}$. $S$ is an approximate local optimum: $|S|=k$, and every nonempty set $T$ of at most $k$ facilities with $|S\setminus T|\le 24N$ satisfies $\mathrm{cost}(T)\ge\bigl(1-\tfrac{1}{Nk}\bigr)\mathrm{cost}(S)$.
--
--   For $c^\ast\in O$, $C^\ast$ denotes its optimal cluster (the clients whose nearest center of $O$ is $c^\ast$, ties going to the center of least index) and $\mathrm{cost}_{OPT}(C^\ast)=\sum_{j\in C^\ast}d(j,c^\ast)$. For $c\in S$, $C_c$ is the cluster of $c$ in $S$, defined in the same way, and $\mathrm{cost}_S(D)=\sum_{j\in D}d(j,S)$ for a set $D$ of clients. $\mathrm{per}(C^\ast)$ is the $\varepsilon$-percentile of $C^\ast$: the least value $t=d(j,c^\ast)$, $j\in C^\ast$, such that at least $\varepsilon|C^\ast|$ clients of $C^\ast$ are within distance $t$ of $c^\ast$. $\mathrm{avg}_{OPT}(C^\ast)=\mathrm{cost}_{OPT}(C^\ast)/|C^\ast|$ and $\mathrm{avg}_S(C^\ast)=\mathrm{cost}_S(C^\ast)/|C^\ast|$. With $\eta=89/100$, $x=\mathrm{per}(C^\ast)/\mathrm{avg}_{OPT}(C^\ast)$ ($x=1$ if $\mathrm{avg}_{OPT}(C^\ast)=0$) and $t=\max(\eta,\min(1,x))$, the parameter $\kappa=\kappa(C^\ast)$ is defined by $1+\kappa=(89-12t)/(65t)$. For $\gamma\ge 0$, $\mathrm{core}_\gamma(C^\ast)=\{j\in C^\ast: d(j,c^\ast)\le(1+\gamma)\,\mathrm{per}(C^\ast)\}$.
--
--   A center $c^\ast\in O$ is *synced* if some $c\in S$ satisfies $|C^\ast\,\triangle\,C_c|\le\varepsilon\,\min(|C^\ast|,|C_c|)$; $\sigma_{sync}(c^\ast)$ is one such $c$, chosen once and for all. A center $c^\ast\in O$ is *close* if it is not synced and $d(c^\ast,S)\le\eta\,\mathrm{avg}_{OPT}(C^\ast)+2\varepsilon\,\mathrm{avg}_S(C^\ast)$; $\sigma_{cl}(c^\ast)$ is the center of $S$ nearest to $c^\ast$ (of least index among the nearest ones). $O_{sync}$ and $O_{cl}$ are the sets of synced and of close centers. Put $O_{S0}=O_{sync}\cup O_{cl}$, $O_1=O\setminus O_{S0}$, and let $\sigma_0$ be $\sigma_{sync}$ on synced centers and $\sigma_{cl}$ on all others.
--
--   A *dummy* $\lambda=(\ell,r)$ is a point $\ell$ (its leader, a client or a facility) with a real radius $r$; its distance to a point $a$ is $d(a,\lambda)=d(a,\ell)+r$, and its *ball* is the set of facilities within distance $r$ of $\ell$. For a set $F$ of facilities and a list $\Lambda$ of dummies, the *mixed set* $(F,\Lambda)$ has $d(a,(F,\Lambda))=\min\bigl(d(a,F),\min_{\lambda\in\Lambda}d(a,\lambda)\bigr)$ and $\mathrm{cost}(F,\Lambda)=\sum_j d(j,(F,\Lambda))$.
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
--   **Statement.** Let $\Lambda_1$ be a good outcome of the client sampling. Let $LS'$ be a set of facilities, $\Lambda_2$ a list of dummies, $M$ a set of facilities and $\varphi$ a map from facilities to dummies such that
--
--   1. $LS_X\subseteq LS'\subseteq S$;
--   2. $M\subseteq O_2\setminus O_X$;
--   3. $\Gamma\bigl((O_2\setminus O_X)\setminus M\bigr)\subseteq LS'$: the unmatched clusters keep all their satellites;
--   4. for every $c^\ast\in M$, the dummy $\varphi(c^\ast)=(\ell,r)$ is an entry of $\Lambda_2$ and $d(c^\ast,\ell)\le r\le(1+\kappa+6\varepsilon)\,\mathrm{per}(C^\ast)$.
--
--   Then, for the concatenation $\Lambda_1\Lambda_2$ of the two lists,
--
--   $$\mathrm{cost}(LS',\Lambda_1\Lambda_2)\;<\;6\,\mathrm{opt}.$$
--
--   In the analysis of the cluster sampling (Algorithm 2), the state $(LS',\Lambda_2)$ after any number of steps that keep the invariant satisfies these conditions, with $M$ the clusters matched so far. The bound is used when the algorithm samples a center with weight the cost of its cluster: the centers that are good to sample have total weight at least $\varepsilon^3\,\mathrm{opt}$, out of a total weight of less than $6\,\mathrm{opt}$, which enters the lower bound $1/(12N^3)$ on the fraction of coin chunks for which a step keeps the invariant.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), Section 4.7. Lean source: `BCFGJPSSV26.Stable.Hyp.costMix_intermediate_lt`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Structure/ClusterWitness.lean#L359-L412

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

theorem costMix_intermediate_lt {Λ₁ : List (Dummy X.I)} (w₁ : ClientWitness X Λ₁)
    {LS' : Finset (Fin X.I.m)} {Λ₂ : List (Dummy X.I)} {M : Finset (Fin X.I.m)}
    {φ : Fin X.I.m → Dummy X.I} (hX : X.LSX w₁.OL ⊆ LS') (hS : LS' ⊆ X.S)
    (hM : M ⊆ X.O2 w₁.OL \ X.OX w₁.OL) (hΓ : X.GamOf (X.OB w₁.OL M) ⊆ LS')
    (hφ : ∀ c ∈ M, φ c ∈ Λ₂ ∧ X.I.dd (.inr c) (φ c).leader ≤ (φ c).radius ∧
      (φ c).radius ≤ (1 + X.kap c + 6 * X.ε) * X.per c) :
    costMix X.I LS' (Λ₁ ++ Λ₂) < 6 * X.opt := by sorry

end Hyp
end BCFGJPSSV26.Stable
end
