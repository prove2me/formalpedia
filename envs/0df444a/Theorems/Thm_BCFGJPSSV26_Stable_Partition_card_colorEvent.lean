-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_Partition_card_colorEvent
-- name    : BCFGJPSSV26.Stable.Partition.card_colorEvent
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:46:02.078935+00:00
-- url     : https://prove2.me/theorems/7b728ff0-5ca4-43bb-9d55-c80bbe645f5d
-- title:
--   Color coding (Part II, Section 3.3) — the color event holds for at least $4^{-s}$ of the colorings
-- statement:
--   The color-coding step of Part II (arXiv:2610.17172), Section 3.3: when the kept centers are colored red or blue by independent fair bits, the color event of a structural partition has probability at least $4^{-s}$.
--
--   **Setting (the standing hypotheses of Part II, Sections 3–6).** Let $N\ge 201$ be an integer and $\varepsilon=1/N$. Let $I$ be a valid $k$-median instance (clients and $m$ facilities with a rational pseudometric $d$) with $2\le k\le m$ and $\mathrm{opt}:=\mathrm{opt}_k>0$, where $\mathrm{opt}_\ell$ is the least cost of a nonempty set of at most $\ell$ facilities. Assume $I$ is $\beta$-stable for some $\beta>0$, i.e. $\mathrm{opt}_{k-1}\ge(1+\beta)\,\mathrm{opt}_k$, and let $L\ge 1/\beta$ be a natural number. Put $s=632NL$ and $b=|\mathrm{enc}(I)|+7N$, where $|\mathrm{enc}(I)|$ is the length of the binary encoding of $I$. Let $O$ be a set of exactly $k$ facilities with $\mathrm{cost}(O)=\mathrm{opt}$, and let $S$ be an approximate local optimum: $|S|=k$, and $\mathrm{cost}(T)\ge\bigl(1-\tfrac{1}{Nk}\bigr)\mathrm{cost}(S)$ for every nonempty set $T$ of at most $k$ facilities with $|S\setminus T|\le 24N$.
--
--   **Data.** Let $\Lambda_1$ be a list of dummies with a certificate that it is a good outcome of the client sampling (client-sampling theorem, Part II, Section 4.2). Let $LS'$ be a list of distinct facility indices (each less than $m$) with $|LS'|\le k$, and $\Lambda_2$ a list of dummies, with a certificate that $(LS',\Lambda_2)$ is a good outcome of the cluster sampling (Section 4.4). Let a structural partition for these outcomes be given, in the sense of Part II, Theorems 3.1 and 3.2: the optimal centers are split into $O_S$ (with substitutes in $LS'$), the clusters $O_\Lambda$ of the dummies, $O_P$ and $O_R$, with the bounds of the theorems (in particular $|O_\Lambda|+|O_P|+|O_R|\le s$), together with a set $Z^{\star}\subseteq LS'\setminus LS_\sigma$ of centers to be closed, of size
--   $$|Z^{\star}|=|LS'|+|\Lambda_1|+|\Lambda_2|+|O_P|-k$$
--   (read as $0$ if this is negative), where $LS_\sigma$ is the set of the substitutes of $O_S$ and of the chosen satellites of $O_R$.
--
--   **Coloring.** A vector $u\in\{0,\dots,2^b-1\}^{k}$ colors the center at position $i$ of the list $LS'$ red if $2u_i<2^b$ and blue otherwise. The *color event* holds if every center of $Z^{\star}$ is red and, for every $c\in Z^{\star}$, the center of $LS'\setminus Z^{\star}$ nearest to $c$ (the one of least index among the nearest) is blue, when $LS'\setminus Z^{\star}$ is nonempty.
--
--   **Statement.**
--   $$\#\bigl\{u\in\{0,\dots,2^b-1\}^{k}:\ \text{the color event holds for the coloring given by }u\bigr\}\ \ge\ \bigl(\tfrac14\bigr)^{s}\,\bigl(2^b\bigr)^{k}.$$
--
--   This is the third factor in the probability that a trial of the algorithm is good, after the two samplings. Under the color event, the submodular step with the guess $p'=|O_P|$ produces a candidate of cost at most $\Psi_T+60\varepsilon\,\mathrm{opt}$ (Theorem 3.4).
--
--   **Formalization Note** A trial reserves $k$ chunks for the coloring and uses the first $|LS'|$ of them; the statement counts vectors of $k$ chunks of $b$ coin flips.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), Section 3.3. Lean source: `BCFGJPSSV26.Stable.Partition.card_colorEvent`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Alg/Coloring.lean#L121-L278

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Coins
public import Definitions.Def_BCFGJPSSV26_Stable_Structure_Partition
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Coloring

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

open Classical in

theorem Partition.card_colorEvent {X : Ctx} (H : Hyp X) {Λ₁ : List (Dummy X.I)}
    {w₁ : ClientWitness X Λ₁} {LS' : List ℕ} {Λ₂ : List (Dummy X.I)}
    {w₂ : ClusterWitness w₁ (X.I.centers LS') Λ₂} (Q : Partition w₂) (hnd : LS'.Nodup)
    (hm : ∀ i ∈ LS', i < X.I.m) (hk : LS'.length ≤ X.I.k) :
    (1 / 4 : ℝ) ^ X.s * ((2 : ℝ) ^ X.b) ^ X.I.k ≤
      (univ.filter fun u : Fin X.I.k → Fin (2 ^ X.b) ↦
        Q.ColorEvent (X.I.centers (redOf LS' (colors X.b LS' (toCh u))))
          (X.I.centers (blueOf LS' (colors X.b LS' (toCh u))))).card := by sorry

end BCFGJPSSV26.Stable
end
