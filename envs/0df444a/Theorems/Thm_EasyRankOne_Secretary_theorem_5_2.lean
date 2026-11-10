-- Prove2me | Theorems.Thm_EasyRankOne_Secretary_theorem_5_2
-- name    : EasyRankOne.Secretary.theorem_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:07:16.360955+00:00
-- url     : https://prove2.me/theorems/92a8ba22-2d19-4265-8b21-cc84a80ad491
-- title:
--   Theorem 5.2 — the survivor family is feasible; Algorithm 3 accepts Greedy(V) independently, each with probability p ln(1/p)
-- statement:
--   Fix $p\in[1/e,1)$ and a matroid $M=(V,\mathcal I)$ on a finite ground set with a fixed label order. With $z$ given by (12), the survivor distributions $\mathcal D_{O,t}$ satisfy capacity (8) and consistency (9). Hence Algorithm 3 — an ordinal algorithm of the continuous-time model — accepts the elements of $\mathrm{Greedy}(V)$ independently, each with probability $p\ln(1/p)$: for every nonnegative value assignment and every $S\subseteq\mathrm{Greedy}(V)$,
--   $$\Pr[S\subseteq \mathrm{ALG}]=\big(p\ln(1/p)\big)^{|S|},$$
--   where $\mathrm{ALG}$ is the final accepted set when every element arrives at an independent uniform time in $[0,1]$. For $p=1/e$ this probability is $1/e$.
--
--   This is the existence of an $e$-probability-competitive ordinal algorithm; the goal adds an efficient implementation.
--
--   Differences from the source:
--   - reading: Algorithm 3 is ordinal → Algorithm 3 defined as a rule of the ordinal continuous-time model; ordinal by construction; reason: in this model ordinality is a property of the algorithm class
--   - reading: accepts the elements of Greedy(V) independently, each with probability p ln(1/p) → Pr[S ⊆ ALG] = (p ln(1/p))^{|S|} for every finite S ⊆ Greedy(V) and every nonnegative v; reason: mutual independence with the stated marginals
--   - encoding: capacity (8) and the integral in (9) → capacity almost everywhere on (0,1), as in footnote 2; integrability required in (9); reason: the source identifies accepting masses up to null times, and its integral is an ordinary integrable probability balance
--   - generalization: §4's standing assumption of positive rank → not imposed; reason: in rank 0 every clause holds trivially; specializes to the source
-- source:
--   Abdi, Banihashem, Hajiaghayi, Huang, Mittal, Singla, As Easy as Rank One, STOC 2027 submission (manuscript of November 2026, sha256 f74f3f91…), p. 16, Theorem 5.2; Algorithm 3, p. 17

import Mathlib
import Definitions.Def_EasyRankOne_Secretary_Greedy
import Definitions.Def_EasyRankOne_Secretary_ContinuousTime
import Definitions.Def_EasyRankOne_Secretary_Survivor

namespace EasyRankOne.Secretary

theorem theorem_5_2 {α : Type*} [Fintype α] [LinearOrder α] (M : Matroid α)
    (hE : M.E = Set.univ) (p : ℝ) (hp : p ∈ Set.Ico (Real.exp (-1)) 1) :
    Capacity M (survFamily M p) (zSurv M p) ∧
    Consistency (survFamily M p) (zSurv M p) ∧
    (∀ v : α → ℝ, (∀ a, 0 ≤ v a) → ∀ S : Finset α, (↑S : Set α) ⊆ Greedy M v Set.univ →
        algProb M v (algorithm3 M p) (fun A => S ⊆ A) = (p * Real.log (1 / p)) ^ S.card) ∧
    (p = Real.exp (-1) → p * Real.log (1 / p) = Real.exp (-1)) := by sorry

end EasyRankOne.Secretary
