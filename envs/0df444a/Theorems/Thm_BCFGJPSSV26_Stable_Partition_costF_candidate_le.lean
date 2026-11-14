-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_Partition_costF_candidate_le
-- name    : BCFGJPSSV26.Stable.Partition.costF_candidate_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:49:50.058036+00:00
-- url     : https://prove2.me/theorems/8f824faf-e92d-4c43-a2f9-5b9ab0904ea7
-- title:
--   Theorem 3.4 (Part II) — the submodular candidate costs at most $\Psi_T+60\,\varepsilon\,\mathrm{opt}$
-- statement:
--   This is Theorem 3.4 of Part II: under the color-coding event, the candidate produced by the submodular step for the guess $|O_P|$ costs at most $\Psi_T+60\,\varepsilon\,\mathrm{opt}$, where $\Psi_T$ is a sum of rows over the classes of the structural partition.
--
--   **Standing hypotheses (H).** $I$ is a valid $k$-median instance ($n$ clients, $m$ facilities, rational pseudometric $d$) with $2\le k\le m$ and $\mathrm{opt}:=\mathrm{opt}_k>0$, where $\mathrm{opt}_\ell$ is the least cost of a nonempty set of at most $\ell$ facilities and $\mathrm{cost}(F)=\sum_j d(j,F)$. $N\ge 201$ is an integer and $\varepsilon=1/N$. $\beta>0$ is a real number, $I$ is $\beta$-stable, i.e. $\mathrm{opt}_{k-1}\ge(1+\beta)\,\mathrm{opt}_k$, and $L$ is a natural number with $L\ge 1/\beta$. $O$ is a set of exactly $k$ facilities with $\mathrm{cost}(O)=\mathrm{opt}$. $S$ is an approximate local optimum: $|S|=k$, and every nonempty set $T$ of at most $k$ facilities with $|S\setminus T|\le 24N$ satisfies $\mathrm{cost}(T)\ge\bigl(1-\tfrac{1}{Nk}\bigr)\mathrm{cost}(S)$.
--
--   For $c^\ast\in O$, $C^\ast$ denotes its optimal cluster (the clients whose nearest center of $O$ is $c^\ast$, ties going to the center of least index) and $\mathrm{cost}_{OPT}(C^\ast)=\sum_{j\in C^\ast}d(j,c^\ast)$. For $c\in S$, $C_c$ is the cluster of $c$ in $S$, defined in the same way, and $\mathrm{cost}_S(D)=\sum_{j\in D}d(j,S)$ for a set $D$ of clients. $\mathrm{per}(C^\ast)$ is the $\varepsilon$-percentile of $C^\ast$: the least value $t=d(j,c^\ast)$, $j\in C^\ast$, such that at least $\varepsilon|C^\ast|$ clients of $C^\ast$ are within distance $t$ of $c^\ast$. $\mathrm{avg}_{OPT}(C^\ast)=\mathrm{cost}_{OPT}(C^\ast)/|C^\ast|$ and $\mathrm{avg}_S(C^\ast)=\mathrm{cost}_S(C^\ast)/|C^\ast|$. With $\eta=89/100$, $x=\mathrm{per}(C^\ast)/\mathrm{avg}_{OPT}(C^\ast)$ ($x=1$ if $\mathrm{avg}_{OPT}(C^\ast)=0$) and $t=\max(\eta,\min(1,x))$, the parameter $\kappa=\kappa(C^\ast)$ is defined by $1+\kappa=(89-12t)/(65t)$. For $\gamma\ge 0$, $\mathrm{core}_\gamma(C^\ast)=\{j\in C^\ast: d(j,c^\ast)\le(1+\gamma)\,\mathrm{per}(C^\ast)\}$.
--
--   A *dummy* $\lambda=(\ell,r)$ is a point $\ell$ (its leader, a client or a facility) with a real radius $r$; its distance to a point $a$ is $d(a,\lambda)=d(a,\ell)+r$, and its *ball* is the set of facilities within distance $r$ of $\ell$. For a set $F$ of facilities and a list $\Lambda$ of dummies, the *mixed set* $(F,\Lambda)$ has $d(a,(F,\Lambda))=\min\bigl(d(a,F),\min_{\lambda\in\Lambda}d(a,\lambda)\bigr)$ and $\mathrm{cost}(F,\Lambda)=\sum_j d(j,(F,\Lambda))$.
--
--   Let $\Lambda_1$ be a good outcome of the client sampling and $(LS',\Lambda_2)$ a good outcome of the cluster sampling (in the sense of the client-sampling and cluster-sampling theorems of Part II, Sections 4.2 and 4.4), and let $Q$ be a structural partition for them: the data $(O_P,O_R,\psi,\sigma,Z^\ast)$ with all the properties stated in the structural theorem (Part II, Theorems 3.1 and 3.2). It splits $O$ into four disjoint classes:
--
--   - $O_S$: the synced and close centers and the centers missed by the client sampling whose core is expensive in $S$; each has a substitute in $S$;
--   - $O_\Lambda$: the centers matched with a dummy of $\Lambda_1$ or $\Lambda_2$; among them $O_\Lambda^e$, the *early* ones, are those of the client sampling whose dummy is led by a client of $\mathrm{core}_{6\varepsilon}(C^\ast)$;
--   - $O_P$: the centers within $(1+\kappa+4\varepsilon)\,\mathrm{per}(C^\ast)$ of a substitute;
--   - $O_R$: the centers with a satellite of their own.
--
--   Write $\Lambda=\Lambda_1\Lambda_2$ for the concatenated list and $z=\max(0,|LS'|+|\Lambda|+|O_P|-k)$; $Z^\ast\subseteq LS'$ is the set of $z$ centers of the partition to be closed. For sets *red* and *blue* of facilities, write $M'=(LS',\Lambda)$; for a facility $c$, let $M_c$ be its cluster in $M'$: the clients whose nearest facility of $LS'$ is $c$ (ties to the least index) and that are at least as near to $LS'$ as to every dummy of $\Lambda$; and let $\mathrm{cost}_{M'}(E)=\sum_{j\in E}d(j,M')$. For a set $Y$ of facilities define
--
--   $$g_1(Y)=\sum_{j}\min\bigl(d(j,M'),\,d(j,Y)\bigr),\qquad h_c(Y)=\mathrm{cost}_{M'}(M_c)+|M_c|\cdot d\bigl(c,(\mathrm{blue}\cup Y,\Lambda)\bigr),$$
--
--   $$g_2(Y)=\min_{Z\subseteq\mathrm{red},\ |Z|=z}\ \sum_{c\in Z}h_c(Y),\qquad g(Y)=g_1(Y)+g_2(Y),$$
--
--   so that $g_2(Y)$ is the sum of the $z$ smallest values $h_c(Y)$ over red $c$.
--
--   **Hypotheses.** Let red $\subseteq LS'$, blue $=LS'\setminus$ red, and let $Y,\hat Z$ be sets of facilities such that
--
--   1. (*color event*) $Z^\ast\subseteq$ red, and for every $c\in Z^\ast$ the center of $LS'\setminus Z^\ast$ nearest to $c$ (of least index among the nearest; if $LS'\setminus Z^\ast\ne\emptyset$) is blue;
--   2. every ball of a dummy of $\Lambda$ contains a facility of $Y$;
--   3. $\hat Z\subseteq$ red, $|\hat Z|=z$ and $\sum_{c\in\hat Z}h_c(Y)=g_2(Y)$;
--   4. (*greedy guarantee with $N$ rounds for the guess $|O_P|$*) for every choice of one facility $o_i$ in the ball of the $i$-th dummy of $\Lambda$ and every set $E$ of exactly $|O_P|$ facilities,
--   $$\Bigl(1-\bigl(\tfrac{N}{N+1}\bigr)^{N}\Bigr)\bigl(g(\emptyset)-g(\{o_i\}_i\cup E)\bigr)\;\le\;g(\emptyset)-g(Y).$$
--
--   **Conclusion.**
--
--   $$\mathrm{cost}\bigl((LS'\setminus\hat Z)\cup Y\bigr)\;\le\;\Psi_T+60\,\varepsilon\,\mathrm{opt},\qquad \Psi_T=\sum_{c^\ast\in O}\mathrm{row}_T(c^\ast),$$
--
--   $$\mathrm{row}_T(c^\ast)=\begin{cases}(1+\eta)\,\mathrm{cost}_{OPT}(C^\ast), & c^\ast\in O_S,\\ \mathrm{cost}_{OPT}(C^\ast)+\tfrac{2}{e}\,|C^\ast|\,\mathrm{per}(C^\ast), & c^\ast\in O_\Lambda^e,\\ \mathrm{cost}_{OPT}(C^\ast)+\tfrac{2}{e}\,(1+\kappa)\,|C^\ast|\,\mathrm{per}(C^\ast), & c^\ast\in(O_\Lambda\setminus O_\Lambda^e)\cup O_P,\\ \mathrm{cost}_{OPT}(C^\ast)+|C^\ast|\,\mathrm{per}(C^\ast), & c^\ast\in O_R.\end{cases}$$
--
--   This is the second bound of the win-win argument: with the nuanced local-search bound $\mathrm{cost}(S)\le\Psi_{LS}+150\,\varepsilon\,\mathrm{opt}$ (Theorem 3.8) and the row inequalities of Lemma 3.9, the local search or this candidate costs at most $(1.89+100\,\varepsilon)\,\mathrm{opt}$. In the algorithm, hypotheses 2–4 hold by construction of the submodular step for the correct guess, and hypothesis 1 holds with probability at least $4^{-s}$ over the coloring.
--
--   **Formalization Note** $Q$ is a term of the Lean structure for the structural partition, whose fields are the properties in the statement of the structural theorem; $e$ in the rows is Euler's number.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), Theorem 3.4. Lean source: `BCFGJPSSV26.Stable.Partition.costF_candidate_le`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Submod/Candidate.lean#L746-L797

module

public import Definitions.Def_BCFGJPSSV26_Stable_Structure_Partition
public import Definitions.Def_BCFGJPSSV26_Stable_Submod_SeqGreedy
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_BCFGJPSSV26_Stable_Submod_Candidate

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

variable {I : Instance}

namespace Partition

variable {X : Ctx} {Λ₁ : List (Dummy X.I)} {w₁ : ClientWitness X Λ₁}
  {LS' : Finset (Fin X.I.m)} {Λ₂ : List (Dummy X.I)} {w₂ : ClusterWitness w₁ LS' Λ₂}
  (Q : Partition w₂)

theorem costF_candidate_le (H : Hyp X) {red blue : Finset (Fin X.I.m)} (hred : red ⊆ LS')
    (hblue : blue = LS' \ red) (hcol : Q.ColorEvent red blue) {Y Zh : Finset (Fin X.I.m)}
    (hY : ∀ l ∈ Λ₁ ++ Λ₂, ∃ i ∈ Y, i ∈ l.ball) (hZ : Zh ⊆ red) (hZc : Zh.card = Q.z)
    (hZs : ∑ c ∈ Zh, hcl X.I LS' (Λ₁ ++ Λ₂) blue c Y = g₂ X.I LS' (Λ₁ ++ Λ₂) red blue Q.z Y)
    (hG : GreedyGuarantee X.I X.P.N (gfun X.I LS' (Λ₁ ++ Λ₂) red blue Q.z) (Λ₁ ++ Λ₂)
      Q.OP.card Y) :
    X.I.costF ((LS' \ Zh) ∪ Y) ≤ Q.PsiT + 60 * X.ε * X.opt := by sorry

end Partition
end BCFGJPSSV26.Stable
end
