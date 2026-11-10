-- Prove2me | Theorems.Thm_AlmostLinSubsetSum_Main_lemma_9_2
-- name    : AlmostLinSubsetSum.Main.lemma_9_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:29:42.079978+00:00
-- url     : https://prove2.me/theorems/56edf388-4ece-4fe2-b699-b5a9e49bf87e
-- title:
--   Lemma 9.2 — growth of repeated sumsets: $|bsA|=O_{\alpha,b}(|sA|)$ and $|sA|\ge c_\alpha(s/t)^{r_\alpha}|tA|$
-- statement:
--   **Lemma 9.2** (p. 42). Fix $\alpha>0$, and let $r_\alpha$ be the rank bound of Theorem 9.A. There is a constant $c_\alpha\in(0,c'_\alpha]$, with $c'_\alpha$ the constant of Theorem 9.A, such that the following holds. Let $A\subseteq[0,L]_{\mathbb Z}$ contain $0$, and let $s\ge L^\alpha$ be an integer that is sufficiently large in terms of $\alpha$. Then for every integer $b\ge1$ and every integer $t\ge s$,
--   $$|bsA|=O_{\alpha,b}(|sA|)\quad(41),\qquad |sA|\ge c_\alpha(s/t)^{r_\alpha}|tA|\quad(42).$$
--
--   Formally: for every $\alpha>0$ there are $r_\alpha\in\mathbb N$, $c'_\alpha>0$, $c_\alpha\in(0,c'_\alpha]$ and $s_0$ such that (a) the conclusion of Theorem 9.A holds with $r_\alpha,c'_\alpha$ for all $s\ge s_0$ (this ties the constants to Theorem 9.A); (b) for every integer $b\ge1$ there is $C_b$ with $|bsA|\le C_b|sA|$ for all $L$, $A$, $s$ as above; (c) $c_\alpha(s/t)^{r_\alpha}|tA|\le|sA|$ for all $L,A,s$ as above and every integer $t\ge s$. Here $kA$ is the $k$-fold sumset.
--
--   Differences from the source:
--   - reading: r_α, c'_α 'the constants of Theorem 9.A' → r_α, c'_α existentially quantified together with a conjunct stating Theorem 9.A's conclusion with them for all s ≥ s₀; reason: the lemma refers to Theorem 9.A's constants; Theorem 9.A only asserts that such constants exist
--   - reading: 's sufficiently large in terms of α' → s ≥ s₀, one s₀ for both (41) and (42), chosen before b; reason: explicit form of 'sufficiently large'
--   - reading: |bsA| = O_{α,b}(|sA|) → ∀ b ≥ 1 ∃ C_b ∀ L A s: |bsA| ≤ C_b |sA|; reason: explicit form of O_{α,b}: the constant depends on α and b only
--   - encoding: X ⊆ [0, L]_ℤ → L ∈ ℕ and X ⊆ Icc 0 L in ℤ; reason: [0, L]_ℤ = [0, ⌊L⌋]_ℤ and L^α ≥ ⌊L⌋^α, so the statement for real L ≥ 0 follows from the one for natural L
-- source:
--   Chen, Mao, Zhang (2026), An Almost-Linear Time Algorithm for Multidimensional Subset Sum, STOC 2027 submission, SHA-256 0cd42ca048cfff088013ad06450a278a6df72a29004c48c5c138f3f6df85d1e0, Lemma 9.2, p. 42

import Mathlib
import Definitions.Def_AlmostLinSubsetSum_Main_Basic
import Definitions.Def_AlmostLinSubsetSum_Main_GAP

set_option autoImplicit false

namespace AlmostLinSubsetSum.Main

/-- **Lemma 9.2** (Growth of repeated sumsets; Chen, Mao, Zhang 2026, p. 42). Fix `α > 0`,
and let `r_α` be the rank bound of Theorem 9.A. There is a constant `c_α ∈ (0, c'_α]`, with
`c'_α` the constant of Theorem 9.A, such that: if `A ⊆ [0, L]_ℤ` contains `0` and `s ≥ L^α`
is an integer sufficiently large in terms of `α`, then for every integer `b ≥ 1` and every
integer `t ≥ s`, `|bsA| = O_{α,b}(|sA|)` (41) and `|sA| ≥ c_α (s/t)^{r_α} |tA|` (42).

Here the constants `r_α, c'_α` are tied to Theorem 9.A by the first conjunct (its conclusion
with these constants for all `s ≥ s₀`); the `O_{α,b}` constant `C_b` is chosen after `b` and
before `L, A, s`. -/
theorem lemma_9_2 :
    ∀ α : ℝ, 0 < α →
    ∃ rα : ℕ, ∃ c' : ℝ, 0 < c' ∧ ∃ cα : ℝ, 0 < cα ∧ cα ≤ c' ∧ ∃ s₀ : ℕ,
    -- Theorem 9.A holds with the constants `r_α`, `c'_α` for all `s ≥ s₀`
    (∀ (L : ℕ) (X : Set ℤ), X ⊆ Set.Icc (0 : ℤ) L → (0 : ℤ) ∈ X →
      ∀ s : ℕ, s₀ ≤ s → (L : ℝ) ^ α ≤ (s : ℝ) →
        ∃ P : GAP, P.IsCentered ∧ P.rank ≤ rα ∧ X ⊆ P.carrier ∧
          P.IsDilateProper (c' * s) ∧
          ∃ z : ℤ, intTranslate z (P.dilateSet (c' * s)) ⊆ kFold s X) ∧
    -- (41)
    (∀ b : ℕ, 1 ≤ b → ∃ Cb : ℝ,
      ∀ (L : ℕ) (A : Set ℤ), A ⊆ Set.Icc (0 : ℤ) L → (0 : ℤ) ∈ A →
      ∀ s : ℕ, s₀ ≤ s → (L : ℝ) ^ α ≤ (s : ℝ) →
        ((kFold (b * s) A).ncard : ℝ) ≤ Cb * (kFold s A).ncard) ∧
    -- (42)
    (∀ (L : ℕ) (A : Set ℤ), A ⊆ Set.Icc (0 : ℤ) L → (0 : ℤ) ∈ A →
      ∀ s : ℕ, s₀ ≤ s → (L : ℝ) ^ α ≤ (s : ℝ) →
      ∀ t : ℕ, s ≤ t →
        cα * ((s : ℝ) / t) ^ rα * (kFold t A).ncard ≤ ((kFold s A).ncard : ℝ)) := by sorry

end AlmostLinSubsetSum.Main
