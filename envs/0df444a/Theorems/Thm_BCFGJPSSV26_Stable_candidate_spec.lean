-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_candidate_spec
-- name    : BCFGJPSSV26.Stable.candidate_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:47:11.808084+00:00
-- url     : https://prove2.me/theorems/7919b050-0e46-459e-b312-9ea165fa9b63
-- title:
--   Submodular step (Part II, Section 5) — specification of a computed candidate
-- statement:
--   Specification of the submodular step of Part II (arXiv:2610.17172), Section 5, as the algorithm computes it in exact arithmetic for one guess $p'$: a computed candidate has the form $(LS'\setminus\hat Z)\cup\hat Y$ of the paper, and $\hat Y$ satisfies the guarantee of the sequential greedy with $N$ rounds.
--
--   **Setting.** Let $I$ be a valid $k$-median instance with $m$ facilities and a rational pseudometric $d$. Let $LS'$ be a list of distinct facility indices (each less than $m$), $\Lambda$ a list of dummies $(\ell,r)$, each a point $\ell$ of $I$ with a rational radius $r$, and $\mathrm{col}$ a list of Booleans of the same length as $LS'$, coloring the center at each position red (true) or blue (false); let $\mathrm{Red}$ and $\mathrm{Blue}$ be the sets of red and blue centers. Let $N\ge1$, $s$, $B$, $p'$ be natural numbers with $N^{|\Lambda|+p'}\le B$, and
--   $$z=|LS'|+|\Lambda|+p'-k\quad(\text{read as }0\text{ if negative}).$$
--   The ball of a dummy $(\ell,r)$ is the set of facilities within $r$ of $\ell$. For a mixed set $M=(F,\Lambda)$, $d(a,M)=\min\bigl(d(a,F),\min_{(\ell,r)\in\Lambda}(d(a,\ell)+r)\bigr)$; with $M'=(LS',\Lambda)$, the cluster $M'_c$ of $c\in LS'$ consists of the clients whose nearest facility of $LS'$ is $c$ and that are not strictly nearer to a dummy. For a set $Y$ of facilities,
--   $$g_1(Y)=\sum_{j}\min\bigl(d(j,M'),d(j,Y)\bigr),\qquad h_c(Y)=\sum_{j\in M'_c}d(j,M')+|M'_c|\;d\bigl(c,(\mathrm{Blue}\cup Y,\Lambda)\bigr),$$
--   $g_2(Y)$ is the sum of the $z$ smallest values $h_c(Y)$, $c\in\mathrm{Red}$, and $g=g_1+g_2$.
--
--   **The candidate.** The guess is skipped if $|\Lambda|+p'>s$, or $z>|\mathrm{Red}|$, or some ball is empty. Otherwise $\hat Y$ is computed by the sequential greedy with $N$ rounds for $g$ over the parts given by the balls of the dummies and $p'$ copies of the set of all facilities, its sums over $N^{|\Lambda|+p'}$ tuples being enumerated within the budget $B$; $\hat Z$ consists of the $z$ red centers of least $h_c(\hat Y)$; and the candidate is the list $(LS'\setminus\hat Z)\cup\hat Y$ without repetitions.
--
--   **Statement.** If the guess is not skipped and $T$ is the computed candidate, then $T$ is a list of distinct facility indices, each less than $m$, with $|T|\le k$, and there are sets $Y$, $\hat Z$ of facilities such that
--
--   1. the set of facilities of $T$ is $(LS'\setminus\hat Z)\cup Y$;
--   2. $Y$ contains a facility of the ball of every dummy of $\Lambda$;
--   3. $\hat Z\subseteq\mathrm{Red}$, $|\hat Z|=z$ and $\sum_{c\in\hat Z}h_c(Y)=g_2(Y)$;
--   4. for every choice of facilities $o_1,\dots,o_{|\Lambda|}$ with $o_i$ in the ball of the $i$-th dummy, and every set $E$ of exactly $p'$ facilities,
--   $$\Bigl(1-\bigl(\tfrac{N}{N+1}\bigr)^{N}\Bigr)\Bigl(g(\emptyset)-g\bigl(\{o_1,\dots,o_{|\Lambda|}\}\cup E\bigr)\Bigr)\ \le\ g(\emptyset)-g(Y).$$
--
--   These are exactly the hypotheses under which the candidate of the guess $p'=|O_P|$ costs at most $\Psi_T+60\varepsilon\,\mathrm{opt}$ (Part II, Theorem 3.4), given good outcomes of the two samplings and the color event; the specification connects the computed object with that analysis in the proof that a trial is good with probability at least $N^{-200s}$.
--
--   **Formalization Note** The distance to the empty set of facilities is the finite number $1+\sum_{a,b}d(a,b)$, larger than every distance, where the paper has $\infty$; this is the convention in $g(\emptyset)$ and in $d(j,Y)$ for $Y=\emptyset$. The hypothesis that $\mathrm{col}$ and $LS'$ have the same length is part of the formal statement.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), Section 5. Lean source: `BCFGJPSSV26.Stable.candidate_spec`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Alg/Submod.lean#L1002-L1037

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Mixed
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Coloring
public import Definitions.Def_BCFGJPSSV26_Stable_Submod_Candidate
public import Definitions.Def_BuhaiPapers_Background_Tuples
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Submod

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26

namespace Raw

open Stable

end Raw

namespace Stable

section Helpers

open Finset

section Greedy

variable (g : List ℕ → ℚ) (parts : List (List ℕ)) (Vs : List (List ℕ))

end Greedy

variable {I : Instance}

end Helpers

variable {I : Instance}

open Classical in

theorem candidate_spec (hv : I.Valid) {N s B : ℕ} (hN : 1 ≤ N) {LS' : List ℕ}
    (hnd : LS'.Nodup) (hm : ∀ i ∈ LS', i < I.m) {Λ : List DumQ} (hΛ : (toRaw I).ValidDums Λ)
    {col : List Bool} (hcol : col.length = LS'.length) {p' : ℕ} (hB : N ^ (Λ.length + p') ≤ B)
    {T : List ℕ} (hT : candidate N (toRaw I) s B LS' Λ col p' = some T) :
    T.Nodup ∧ (∀ i ∈ T, i < I.m) ∧ T.length ≤ I.k ∧
      ∃ Y Zh : Finset (Fin I.m), I.centers T = (I.centers LS' \ Zh) ∪ Y ∧
        (∀ l ∈ toDums I Λ, ∃ i ∈ Y, i ∈ l.ball) ∧ Zh ⊆ I.centers (redOf LS' col) ∧
        Zh.card = (LS'.length + (Λ.length + p')) - I.k ∧
        ∑ c ∈ Zh, hcl I (I.centers LS') (toDums I Λ) (I.centers (blueOf LS' col)) c Y =
          g₂ I (I.centers LS') (toDums I Λ) (I.centers (redOf LS' col))
            (I.centers (blueOf LS' col)) ((LS'.length + (Λ.length + p')) - I.k) Y ∧
        GreedyGuarantee I N (gfun I (I.centers LS') (toDums I Λ) (I.centers (redOf LS' col))
          (I.centers (blueOf LS' col)) ((LS'.length + (Λ.length + p')) - I.k))
          (toDums I Λ) p' Y := by sorry

end Stable
end BCFGJPSSV26
end
