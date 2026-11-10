-- Prove2me | Theorems.Thm_EasyRankOne_Secretary_lemma_5_3
-- name    : EasyRankOne.Secretary.lemma_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:07:27.675267+00:00
-- url     : https://prove2.me/theorems/8c006554-b697-456a-8690-c26b4bfda741
-- title:
--   Lemma 5.3 — capacity comparison D_{O,t,H}(A) ≥ (p/σ_{e,H}) D_{O,t,H+e}(A) for every background schedule
-- statement:
--   Fix $p\in[1/e,1)$, a horizon $t\in[p,1]$ and an ordered set $O$. For every background schedule $H$ disjoint from $O$ (fixed auxiliary times in $[0,t]$), every $e\notin O$ (possibly already in the background, in which case $H+e$ lowers its auxiliary time to $p$), and every $A\subseteq O$,
--   $$\mathcal D_{O,t,H}(A)\ \ge\ \frac{p}{\sigma_{e,H}}\,\mathcal D_{O,t,H+e}(A). \tag{13}$$
--   With empty background and a nonloop $e$, $\sigma_{e,\emptyset}=t$, giving the capacity bound $\mathcal D_{O,t}(A)\ge \frac pt\,\mathcal D_{O,t,e}(A)$.
--
--   This is the capacity half of the feasibility of the survivor family (Theorem 5.2), and its inductive proof is the blueprint of the efficient implementation (Lemma 6.2).
--
--   Differences from the source:
--   - encoding: background schedules, H + e, σ_{e,H} → `Background α = α → Option ℝ`, `bgAdd H e p` (keeps the earlier time), `bgSpan` (sInf of the spanning times in [p, t], t if none); reason: Lean convention, same objects
--   - encoding: the last sentence → a second clause: for a nonloop e ∉ O, σ_{e,∅} = t and D_{O,t}(A) ≥ (p/t) D_{O,t,e}(A) for A ⊆ O; reason: the sentence's content as a statement
--   - generalization: §4's standing assumption "positive rank" → not imposed; reason: in rank 0 every element is a loop, all survivor distributions are the point mass at ∅ and σ_{e,H} = p, so the inequality holds with equality; the statement specializes to the source's
-- source:
--   Abdi, Banihashem, Hajiaghayi, Huang, Mittal, Singla, As Easy as Rank One, STOC 2027 submission (manuscript of November 2026, sha256 f74f3f91…), p. 18, Lemma 5.3

import Mathlib
import Definitions.Def_EasyRankOne_Secretary_Greedy
import Definitions.Def_EasyRankOne_Secretary_ContinuousTime
import Definitions.Def_EasyRankOne_Secretary_Survivor

namespace EasyRankOne.Secretary

theorem lemma_5_3 {α : Type*} [Fintype α] [DecidableEq α] (M : Matroid α)
    (hE : M.E = Set.univ) (p : ℝ) (hp : p ∈ Set.Ico (Real.exp (-1)) 1)
    (t : ℝ) (ht : t ∈ Set.Icc p 1) (O : List α) (hO : O.Nodup) :
    (∀ H : Background α, (∀ a ∈ O, H a = none) →
        (∀ a s, H a = some s → s ∈ Set.Icc 0 t) →
        ∀ e : α, e ∉ O → ∀ A : Finset α, A ⊆ O.toFinset →
          p / bgSpan M p t H e * survD M p O t (bgAdd H e p) A ≤ survD M p O t H A) ∧
    (∀ e : α, M.IsNonloop e → e ∉ O →
        bgSpan M p t bgEmpty e = t ∧
        ∀ A : Finset α, A ⊆ O.toFinset →
          p / t * survD M p O t (bgAdd bgEmpty e p) A ≤ survD M p O t bgEmpty A) := by sorry

end EasyRankOne.Secretary
