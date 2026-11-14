-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_Partition_costF_S_le_PsiLS
-- name    : BCFGJPSSV26.Stable.Partition.costF_S_le_PsiLS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:49:30.103863+00:00
-- url     : https://prove2.me/theorems/da24bb04-319c-4ce4-9d6e-07eadbe86062
-- title:
--   Theorem 3.8 (Part II) — nuanced local-search bound $\mathrm{cost}(S)\le\Psi_{LS}+150\,\varepsilon\,\mathrm{opt}$
-- statement:
--   This is the nuanced local-search bound, Theorem 3.8 of Part II: the cost of the local-search solution is bounded cluster by cluster, according to the class of each optimal cluster in the structural partition.
--
--   **Standing hypotheses (H).** $I$ is a valid $k$-median instance ($n$ clients, $m$ facilities, rational pseudometric $d$) with $2\le k\le m$ and $\mathrm{opt}:=\mathrm{opt}_k>0$, where $\mathrm{opt}_\ell$ is the least cost of a nonempty set of at most $\ell$ facilities and $\mathrm{cost}(F)=\sum_j d(j,F)$. $N\ge 201$ is an integer and $\varepsilon=1/N$. $\beta>0$ is a real number, $I$ is $\beta$-stable, i.e. $\mathrm{opt}_{k-1}\ge(1+\beta)\,\mathrm{opt}_k$, and $L$ is a natural number with $L\ge 1/\beta$. $O$ is a set of exactly $k$ facilities with $\mathrm{cost}(O)=\mathrm{opt}$. $S$ is an approximate local optimum: $|S|=k$, and every nonempty set $T$ of at most $k$ facilities with $|S\setminus T|\le 24N$ satisfies $\mathrm{cost}(T)\ge\bigl(1-\tfrac{1}{Nk}\bigr)\mathrm{cost}(S)$.
--
--   For $c^\ast\in O$, $C^\ast$ denotes its optimal cluster (the clients whose nearest center of $O$ is $c^\ast$, ties going to the center of least index) and $\mathrm{cost}_{OPT}(C^\ast)=\sum_{j\in C^\ast}d(j,c^\ast)$. For $c\in S$, $C_c$ is the cluster of $c$ in $S$, defined in the same way, and $\mathrm{cost}_S(D)=\sum_{j\in D}d(j,S)$ for a set $D$ of clients. $\mathrm{per}(C^\ast)$ is the $\varepsilon$-percentile of $C^\ast$: the least value $t=d(j,c^\ast)$, $j\in C^\ast$, such that at least $\varepsilon|C^\ast|$ clients of $C^\ast$ are within distance $t$ of $c^\ast$. $\mathrm{avg}_{OPT}(C^\ast)=\mathrm{cost}_{OPT}(C^\ast)/|C^\ast|$ and $\mathrm{avg}_S(C^\ast)=\mathrm{cost}_S(C^\ast)/|C^\ast|$. With $\eta=89/100$, $x=\mathrm{per}(C^\ast)/\mathrm{avg}_{OPT}(C^\ast)$ ($x=1$ if $\mathrm{avg}_{OPT}(C^\ast)=0$) and $t=\max(\eta,\min(1,x))$, the parameter $\kappa=\kappa(C^\ast)$ is defined by $1+\kappa=(89-12t)/(65t)$. For $\gamma\ge 0$, $\mathrm{core}_\gamma(C^\ast)=\{j\in C^\ast: d(j,c^\ast)\le(1+\gamma)\,\mathrm{per}(C^\ast)\}$.
--
--   Let $\Lambda_1$ be a good outcome of the client sampling and $(LS',\Lambda_2)$ a good outcome of the cluster sampling (in the sense of the client-sampling and cluster-sampling theorems of Part II, Sections 4.2 and 4.4), and let $Q$ be a structural partition for them: the data $(O_P,O_R,\psi,\sigma,Z^\ast)$ with all the properties stated in the structural theorem (Part II, Theorems 3.1 and 3.2). It splits $O$ into four disjoint classes:
--
--   - $O_S$: the synced and close centers and the centers missed by the client sampling whose core is expensive in $S$; each has a substitute in $S$;
--   - $O_\Lambda$: the centers matched with a dummy of $\Lambda_1$ or $\Lambda_2$; among them $O_\Lambda^e$, the *early* ones, are those of the client sampling whose dummy is led by a client of $\mathrm{core}_{6\varepsilon}(C^\ast)$;
--   - $O_P$: the centers within $(1+\kappa+4\varepsilon)\,\mathrm{per}(C^\ast)$ of a substitute;
--   - $O_R$: the centers with a satellite of their own.
--
--   Define the local-search row of $c^\ast\in O$ by
--
--   $$\mathrm{row}_{LS}(c^\ast)=\begin{cases}(1+\eta)\,\mathrm{cost}_{OPT}(C^\ast), & c^\ast\in O_S,\\ 3\,\mathrm{cost}_{OPT}(C^\ast), & c^\ast\in O_\Lambda^e,\\ \mathrm{cost}_{OPT}(C^\ast)+|C^\ast|\,\mathrm{per}(C^\ast), & c^\ast\in (O_\Lambda\setminus O_\Lambda^e)\cup O_P,\\ \mathrm{cost}_{OPT}(K)+2\,\mathrm{cost}_{OPT}(C^\ast\setminus K)+|C^\ast\setminus K|\,\mathrm{per}(C^\ast), & c^\ast\in O_R,\end{cases}$$
--
--   where $K=\mathrm{core}_\kappa(C^\ast)$ and $\mathrm{cost}_{OPT}(D)=\sum_{j\in D}d(j,c^\ast)$ for $D\subseteq C^\ast$, and let $\Psi_{LS}=\sum_{c^\ast\in O}\mathrm{row}_{LS}(c^\ast)$. Then
--
--   $$\mathrm{cost}(S)\;\le\;\Psi_{LS}+150\,\varepsilon\,\mathrm{opt}.$$
--
--   This is one of the two bounds of the win-win argument. The other, Theorem 3.4, bounds the submodular candidate by $\Psi_T+60\,\varepsilon\,\mathrm{opt}$; by Lemma 3.9 the combination with weights $3/25$ and $22/25$ of the two rows of every cluster is at most $(1+\eta+O(\varepsilon))\,\mathrm{cost}_{OPT}(C^\ast)$, so the local search or the candidate costs at most $(1.89+100\,\varepsilon)\,\mathrm{opt}$.
--
--   **Formalization Note** The hypothesis $Q$ is a term of the Lean structure for the structural partition, whose fields are exactly the properties listed in the statement of the structural theorem; the paper's $O(\varepsilon)$ error is the explicit $150\,\varepsilon$, with $\varepsilon=1/N$.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), Theorem 3.8. Lean source: `BCFGJPSSV26.Stable.Partition.costF_S_le_PsiLS`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/LSBound/NiceMaps.lean#L971-L982

module

public import Definitions.Def_BCFGJPSSV26_Stable_Structure_Partition
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_Refined
public import Definitions.Def_BCFGJPSSV26_Stable_LSBound_NiceMaps

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace Partition

variable {X : Ctx} {Λ₁ : List (Dummy X.I)} {w₁ : ClientWitness X Λ₁}
  {LS' : Finset (Fin X.I.m)} {Λ₂ : List (Dummy X.I)} {w₂ : ClusterWitness w₁ LS' Λ₂}
  (Q : Partition w₂)

section Maps

variable (H : Hyp X)

end Maps

theorem costF_S_le_PsiLS (H : Hyp X) : X.I.costF X.S ≤ Q.PsiLS + 150 * X.ε * X.opt := by sorry

end Partition
end BCFGJPSSV26.Stable
end
