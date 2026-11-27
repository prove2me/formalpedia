-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_Supplement_lemma_16
-- name    : BudgetAgg.NashChar.Supplement.lemma_16
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T06:08:14.480215+00:00
-- url     : https://prove2.me/theorems/3cccf957-9c84-466a-a844-f0bad2bd4aa9
-- title:
--   Lemma 16 (used in the proof of Theorem 4) — continuous leximin-strategyproof f: moving to P∗ keeps the outcome on 𝒫+ and the critical sets
-- statement:
--   Let $f$ be a continuous mechanism that is strategyproof for **Leximin-Leontief preferences**. For a profile $P$ put $q=f(P)$ and let $P^*$ be the key profile of p. 33: agent $i$'s peak is moved onto her critical alternatives $T_{q,i}$,
--   $$p^*_{i,j}=\begin{cases}p_{i,j}/p_i(T_{q,i}) & j\in T_{q,i},\\ 0 & j\notin T_{q,i},\end{cases}\qquad p_i(T_{q,i})=\sum_{j\in T_{q,i}}p_{i,j}.$$
--   Then
--
--   1. (a) the outcome does not change, $f(P^*)=f(P)=q$, for every strictly positive profile $P\in\mathcal P^+$ (all $p_{i,j}>0$);
--   2. (b) the sets of critical alternatives do not change, $T_{q,i}=T^*_{q,i}$ for every agent $i$.
--
--   It is the leximin counterpart of Lemma 9 and carries the "only if" direction of Theorem 4 on $\mathcal P^+$; no efficiency or group-strategyproofness is assumed.
--
--   **Formalization Note** $n,m\ge1$. $P^*$ is not a `def`: part (a) asserts the existence of a profile whose peaks are the published `starPeak (P i) q`, which determines it uniquely. Part (b) is stated for every profile $P$ and every $P^*$ built this way, which contains the case $P\in\mathcal P^+$.
--
--   Differences from the source:
--   - encoding: agents N = [n], alternatives M = [m], 1-based → Fin n, Fin m (0-based); distributions and peaks are points of stdSimplex ℝ (Fin m); reason: relabelling only; every instance corresponds
--   - encoding: continuity in the ℓ1 distance (Definition 7) → Continuous f for the subtype/product topology; reason: all norms on a finite-dimensional space induce the same topology, as p. 8 notes
--   - generalization: (b) T_{q,i} = T∗_{q,i}, stated after "for P ∈ 𝒫+" in (a) → (b) holds for every profile P (not only P ∈ 𝒫+) and every P∗ with peaks starPeak (P i) (f P); reason: The proof on pp. 42–44 works on strictly positive profiles. Part (b) is extended to all profiles: crit is nonempty, its peak mass is positive, and starPeak has support exactly crit with a constant ratio there, even when that ratio is zero. This contains every source instance.
--   - encoding: P∗ defined by the case formula of p. 33 → ∃ Ps with (Ps i).1 = starPeak (P i) (f P).1 for all i; reason: starPeak is the case formula; a profile is determined by its peaks
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 42, Lemma 16 (proof pp. 42–44)

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting
import Definitions.Def_BudgetAgg_NashChar_Supplement_Leximin

namespace BudgetAgg.NashChar.Supplement

open BudgetAgg.NashChar

/-- Lemma 16, p. 42: for a continuous Leximin-Leontief-strategyproof mechanism `f`,
(a) on every strictly positive profile `P`, moving to the key profile `P∗` (built from
`q = f(P)` with `starPeak`) keeps the outcome; (b) for every profile, the critical
sets at `q = f(P)` are the same under `P∗` as under `P`. -/
theorem lemma_16 {n m : ℕ} [NeZero n] [NeZero m]
    (f : Mechanism n m) (hf_cont : Continuous f) (hf_sp : IsLexStrategyproof f) :
    (∀ P : Profile n m, (∀ i j, 0 < (P i).1 j) →
      ∃ Ps : Profile n m, (∀ i, (Ps i).1 = starPeak (P i) (f P).1) ∧ f Ps = f P) ∧
    (∀ P Ps : Profile n m, (∀ i, (Ps i).1 = starPeak (P i) (f P).1) →
      ∀ i, crit (Ps i) (f P).1 = crit (P i) (f P).1) := by sorry

end BudgetAgg.NashChar.Supplement
