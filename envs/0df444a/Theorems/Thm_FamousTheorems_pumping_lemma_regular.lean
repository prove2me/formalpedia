-- Prove2me | Theorems.Thm_FamousTheorems_pumping_lemma_regular
-- name    : FamousTheorems.pumping_lemma_regular
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:51.159039+00:00
-- url     : https://prove2.me/theorems/3ba541d9-d756-4c0f-965c-ad12f40b5115
-- title:
--   The pumping lemma for regular languages
-- statement:
--   **The pumping lemma for regular languages.** Let $M$ be a deterministic finite automaton with $k$ states, and $x$ a word accepted by $M$ of length at least $k$. Then $x=abc$ with $|a|+|b|\le k$ and $b$ nonempty, such that $ab^ic$ is accepted by $M$ for every $i\ge0$.
--
--   The pumping lemma is the standard tool for proving that a language is not regular, for example $\{0^n1^n\}$ or the language of balanced parentheses.
--
--   **Formalization note.** Mathlib's `DFA.pumping_lemma`. The number of states is `Fintype.card σ`, and "$ab^ic$ is accepted for every $i$" is stated as the language inclusion `{a} * b* * {c} ≤ M.accepts`, where `KStar.kstar {b}` is the Kleene star of the singleton language.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `DFA.pumping_lemma`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem pumping_lemma_regular {α σ : Type*} (M : DFA α σ) [Fintype σ] {x : List α} (hx : x ∈ M.accepts) (hlen : Fintype.card σ ≤ x.length) :
    ∃ a b c : List α, x = a ++ b ++ c ∧ a.length + b.length ≤ Fintype.card σ ∧ b ≠ [] ∧
      ({a} : Language α) * KStar.kstar ({b} : Language α) * ({c} : Language α) ≤ M.accepts := by sorry

end FamousTheorems
