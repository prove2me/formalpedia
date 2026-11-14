-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_Partition_min_le_bound
-- name    : BCFGJPSSV26.Stable.Partition.min_le_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:48:20.727066+00:00
-- url     : https://prove2.me/theorems/dfbe586c-76c3-4b48-a481-e403b38a42a6
-- title:
--   Win-win (Part II, Section 3.5) — the local search or the candidate costs at most $(1.89+100\varepsilon)\,\mathrm{opt}$
-- statement:
--   The final bound of the win-win argument of Part II (arXiv:2610.17172), Section 3.5: given a structural partition, the local-search solution, or any solution whose cost is within $60\varepsilon\,\mathrm{opt}$ of the submodular bound $\Psi_T$, costs at most $(1+\eta+100\varepsilon)\,\mathrm{opt}$, with $\eta=\tfrac{89}{100}$.
--
--   **Setting (the standing hypotheses of Part II, Sections 3–6).** Let $N\ge 201$ be an integer and $\varepsilon=1/N$. Let $I$ be a valid $k$-median instance (clients and $m$ facilities with a rational pseudometric $d$) with $2\le k\le m$ and $\mathrm{opt}:=\mathrm{opt}_k>0$, where $\mathrm{opt}_\ell$ is the least cost of a nonempty set of at most $\ell$ facilities. Assume $I$ is $\beta$-stable for some $\beta>0$, i.e. $\mathrm{opt}_{k-1}\ge(1+\beta)\,\mathrm{opt}_k$, and let $L\ge 1/\beta$ be a natural number. Put $s=632NL$ and $b=|\mathrm{enc}(I)|+7N$, where $|\mathrm{enc}(I)|$ is the length of the binary encoding of $I$. Let $O$ be a set of exactly $k$ facilities with $\mathrm{cost}(O)=\mathrm{opt}$, and let $S$ be an approximate local optimum: $|S|=k$, and $\mathrm{cost}(T)\ge\bigl(1-\tfrac{1}{Nk}\bigr)\mathrm{cost}(S)$ for every nonempty set $T$ of at most $k$ facilities with $|S\setminus T|\le 24N$.
--
--   **Notation.** For $o\in O$: $C_o$ is its optimal cluster (the clients whose nearest facility of $O$ is $o$), $\mathrm{avg}_O(o)=\frac{1}{|C_o|}\sum_{j\in C_o}d(j,o)$; $\mathrm{per}(o)$ is the $\varepsilon$-percentile, the least distance $t=d(j,o)$, $j\in C_o$, such that at least $\varepsilon|C_o|$ clients of $C_o$ are within $t$ of $o$; $\mathrm{core}_\gamma(o)=\{j\in C_o:\ d(j,o)\le(1+\gamma)\,\mathrm{per}(o)\}$; and $\kappa(o)$ is defined by $1+\kappa=(89-12t)/(65t)$ with $t=\max\bigl(\tfrac{89}{100},\min(1,x)\bigr)$, $x=\mathrm{per}(o)/\mathrm{avg}_O(o)$ ($x=1$ if $\mathrm{avg}_O(o)=0$).
--
--   **Data.** Let $\Lambda_1$ be a list of dummies with a certificate that it is a good outcome of the client sampling (Part II, Section 4.2), with hit clusters $O_{\Lambda1}$ and early clusters $O_\Lambda^{e}\subseteq O_{\Lambda1}$; let $LS'$ be a set of facilities and $\Lambda_2$ a list of dummies with a certificate that $(LS',\Lambda_2)$ is a good outcome of the cluster sampling (Section 4.4), with matched clusters $O_{\Lambda2}$; and let a structural partition for these outcomes be given, in the sense of Part II, Theorems 3.1 and 3.2. It splits $O$ into four disjoint parts: $O_S$ (the centers with a substitute in $LS'$: the synced centers, the close centers and the set $O_{S1}$ of Part II, Section 4), $O_\Lambda=O_{\Lambda1}\cup O_{\Lambda2}$ (the clusters of the dummies), $O_P$ (clusters with a nearby substitute) and $O_R$ (clusters with a satellite), with the bounds of the theorems.
--
--   **Rows.** For $o\in O$ write $A=\mathrm{cost}_O(o)=\sum_{j\in C_o}d(j,o)$, $n=|C_o|$, $p=\mathrm{per}(o)$, $\kappa=\kappa(o)$, and let $K=\mathrm{core}_\kappa(o)$ with $A_K=\sum_{j\in K}d(j,o)$. The local-search row and the submodular row of $o$ are:
--
--   - if $o\in O_S$: $\mathrm{row}_{LS}(o)=(1+\eta)A$ and $\mathrm{row}_T(o)=(1+\eta)A$;
--   - if $o\in O_\Lambda^{e}$: $\mathrm{row}_{LS}(o)=3A$ and $\mathrm{row}_T(o)=A+\tfrac{2}{e}\,np$;
--   - if $o\in(O_\Lambda\cup O_P)\setminus O_\Lambda^{e}$: $\mathrm{row}_{LS}(o)=A+np$ and $\mathrm{row}_T(o)=A+\tfrac{2}{e}(1+\kappa)\,np$;
--   - if $o\in O_R$: $\mathrm{row}_{LS}(o)=A_K+2(A-A_K)+(n-|K|)\,p$ and $\mathrm{row}_T(o)=A+np$;
--
--   with $\eta=\tfrac{89}{100}$, and $\Psi_{LS}=\sum_{o\in O}\mathrm{row}_{LS}(o)$, $\Psi_T=\sum_{o\in O}\mathrm{row}_T(o)$.
--
--   **Statement.** Let $c_T$ be a real number with $c_T\le\Psi_T+60\,\varepsilon\,\mathrm{opt}$. Then
--   $$\mathrm{cost}(S)\ \le\ \Bigl(1+\frac{89}{100}+100\,\varepsilon\Bigr)\mathrm{opt}\qquad\text{or}\qquad c_T\ \le\ \Bigl(1+\frac{89}{100}+100\,\varepsilon\Bigr)\mathrm{opt}.$$
--
--   In the algorithm, $c_T$ is the cost of the candidate of the guess $p'=|O_P|$, which is at most $\Psi_T+60\varepsilon\,\mathrm{opt}$ under the color event (Theorem 3.4). The statement therefore shows that a trial with good outcomes of both samplings and a good coloring contains a solution of cost at most $(1.89+100\varepsilon)\,\mathrm{opt}\le(1.89+1000/N)\,\mathrm{opt}$, the bound of Theorem 1.1 for the accuracy $\varepsilon=1/N$.
--
--   **Formalization Note** Only the row sum $\Psi_T$ of the partition enters the hypothesis on $c_T$; the row sum $\Psi_{LS}$ enters through the bound $\mathrm{cost}(S)\le\Psi_{LS}+150\varepsilon\,\mathrm{opt}$ of Theorem 3.8.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), Section 3.5 (with Lemma 3.9 and Theorem 3.8). Lean source: `BCFGJPSSV26.Stable.Partition.min_le_bound`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Final/Combine.lean#L224-L235

module

public import Definitions.Def_BCFGJPSSV26_Stable_LSBound_NiceMaps
public import Definitions.Def_BCFGJPSSV26_Stable_Submod_Candidate
public import Definitions.Def_BCFGJPSSV26_Stable_WinWin
public import Definitions.Def_BCFGJPSSV26_Stable_Final_Combine

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace Partition

variable {X : Ctx} {Λ₁ : List (Dummy X.I)} {w₁ : ClientWitness X Λ₁}
  {LS' : Finset (Fin X.I.m)} {Λ₂ : List (Dummy X.I)} {w₂ : ClusterWitness w₁ LS' Λ₂}
  (Q : Partition w₂)

theorem min_le_bound (H : Hyp X) {cT : ℝ} (hT : cT ≤ Q.PsiT + 60 * X.ε * X.opt) :
    X.I.costF X.S ≤ (1 + eta + 100 * X.ε) * X.opt ∨ cT ≤ (1 + eta + 100 * X.ε) * X.opt := by sorry

end Partition
end BCFGJPSSV26.Stable
end
