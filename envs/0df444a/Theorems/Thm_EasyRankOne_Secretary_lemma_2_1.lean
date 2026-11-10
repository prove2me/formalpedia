-- Prove2me | Theorems.Thm_EasyRankOne_Secretary_lemma_2_1
-- name    : EasyRankOne.Secretary.lemma_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:05:45.625414+00:00
-- url     : https://prove2.me/theorems/ea56dde1-1ac3-4b0f-bfeb-56cde873c900
-- title:
--   Lemma 2.1 — greedy monotonicity and one-element sensitivity
-- statement:
--   Let $M=(V,\mathcal I)$ be a matroid on a finite ground set with a fixed label order, and let values be nonnegative; $\mathrm{Greedy}_v(T)$ is decreasing-value greedy on $T$ with ties broken by labels. Then:
--
--   (i) If $e\in T\subseteq V$ and $e\in\mathrm{Greedy}_v(V)$, then $e\in\mathrm{Greedy}_v(T)$. More generally, if $v'_e=v_e$ and $v'_f\le v_f$ for all $f\neq e$, then $e\in\mathrm{Greedy}_v(T)$ implies $e\in\mathrm{Greedy}_{v'}(T)$.
--
--   (ii) For $e\notin T$,
--   $$\mathrm{Greedy}(T+e)\in\big\{\mathrm{Greedy}(T),\ \mathrm{Greedy}(T)+e\big\}\ \text{ or }\ \mathrm{Greedy}(T+e)=(\mathrm{Greedy}(T)-f)+e \text{ for one } f\in\mathrm{Greedy}(T).$$
--
--   (iii) If $v'$ differs from $v$ only at $e$, then on a fixed ground set $T$ either $\mathrm{Greedy}_{v'}(T)=\mathrm{Greedy}_v(T)$, or the two differ by exchanging $e$ with one other element $f$ ($e$ enters and $f$ leaves, or $e$ leaves and $f$ enters). If $v'_e\ge v_e$ then $e$ cannot leave; if $v'_e\le v_e$ then $e$ cannot enter.
--
--   These are the standard greedy facts used by the paper's algorithms; (i) is why every optimum element is eligible whenever it arrives.
--
--   Differences from the source:
--   - encoding: Greedy(T) as the output of the greedy scan → the closure form {e ∈ T : e ∉ cl{f ∈ T : f ≻ e}}; reason: the paper states this equivalence itself (p. 5), and it is the same set
--   - encoding: a fixed order of element labels → the `LinearOrder` of the finite ground type `α`, with `M.E = univ`; reason: Lean convention, same instances
--   - reading: (i) "more generally, reducing other values while keeping a selected element's value fixed does not remove it" → a separate clause on a fixed ground set T with v'_e = v_e and v'_f ≤ v_f (f ≠ e), both assignments nonnegative; reason: the sentence's literal content
--   - reading: (iii) "either leaves the greedy basis unchanged or exchanges that element with one other element; an increase can only bring the changed element into the basis; a decrease can only remove it" → unchanged, or one exchange of e with some f ≠ e, plus the implications (v_e ≤ v'_e, e selected ⇒ e selected) and (v'_e ≤ v_e, e not selected ⇒ e not selected); reason: the literal content of the sentence
-- source:
--   Abdi, Banihashem, Hajiaghayi, Huang, Mittal, Singla, As Easy as Rank One, STOC 2027 submission (manuscript of November 2026, sha256 f74f3f91…), p. 5, Lemma 2.1

import Mathlib
import Definitions.Def_EasyRankOne_Secretary_Greedy

namespace EasyRankOne.Secretary

theorem lemma_2_1 {α : Type*} [Fintype α] [LinearOrder α] (M : Matroid α)
    (hE : M.E = Set.univ) :
    (∀ v : α → ℝ, (∀ a, 0 ≤ v a) → ∀ (T : Set α) (e : α),
        e ∈ T → e ∈ Greedy M v Set.univ → e ∈ Greedy M v T) ∧
    (∀ v v' : α → ℝ, (∀ a, 0 ≤ v a) → (∀ a, 0 ≤ v' a) → ∀ (T : Set α) (e : α),
        v' e = v e → (∀ f, f ≠ e → v' f ≤ v f) → e ∈ Greedy M v T → e ∈ Greedy M v' T) ∧
    (∀ v : α → ℝ, (∀ a, 0 ≤ v a) → ∀ (T : Set α) (e : α), e ∉ T →
        Greedy M v (insert e T) = Greedy M v T ∨
        Greedy M v (insert e T) = insert e (Greedy M v T) ∨
        ∃ f ∈ Greedy M v T, Greedy M v (insert e T) = insert e (Greedy M v T \ {f})) ∧
    (∀ v v' : α → ℝ, (∀ a, 0 ≤ v a) → (∀ a, 0 ≤ v' a) → ∀ (T : Set α) (e : α),
        (∀ f, f ≠ e → v' f = v f) →
        (Greedy M v' T = Greedy M v T ∨
          ∃ f, f ≠ e ∧
            ((e ∉ Greedy M v T ∧ f ∈ Greedy M v T ∧
                Greedy M v' T = insert e (Greedy M v T \ {f})) ∨
             (e ∈ Greedy M v T ∧ f ∉ Greedy M v T ∧
                Greedy M v' T = insert f (Greedy M v T \ {e})))) ∧
        (v e ≤ v' e → e ∈ Greedy M v T → e ∈ Greedy M v' T) ∧
        (v' e ≤ v e → e ∉ Greedy M v T → e ∉ Greedy M v' T)) := by sorry

end EasyRankOne.Secretary
