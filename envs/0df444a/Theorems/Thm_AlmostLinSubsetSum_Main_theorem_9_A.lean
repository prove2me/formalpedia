-- Prove2me | Theorems.Thm_AlmostLinSubsetSum_Main_theorem_9_A
-- name    : AlmostLinSubsetSum.Main.theorem_9_A
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:29:35.286875+00:00
-- url     : https://prove2.me/theorems/e22d7de8-ab3a-4cb6-9073-d4a88bbe10be
-- title:
--   Theorem 9.A — long sumsets (Conlon–Fox–Pham): $sX$ contains a translate of a proper $P_{c'_\alpha s}$ of a bounded-rank centered GAP containing $X$
-- statement:
--   **Theorem 9.A** (p. 41; Conlon–Fox–Pham, Lemma 2.22 and Corollary 2.24). For every $\alpha>0$ there are constants $r_\alpha$ and $c'_\alpha>0$ such that the following holds. If $X\subseteq[0,L]_{\mathbb Z}$ contains $0$ and $s\ge L^\alpha$ is an integer that is sufficiently large in terms of $\alpha$, then there is a centered GAP $P$ of rank at most $r_\alpha$ containing $X$ such that $P_{c'_\alpha s}$ is proper and $z+P_{c'_\alpha s}\subseteq sX$ for some $z\in\mathbb Z$, where $sX$ is the $s$-fold sumset.
--
--   Formally: $\forall\alpha>0\ \exists r_\alpha\in\mathbb N,\ c'_\alpha>0,\ s_0$ such that for all $L\in\mathbb N$, all $X\subseteq[0,L]\cap\mathbb Z$ with $0\in X$ and all integers $s\ge s_0$ with $s\ge L^\alpha$, the conclusion holds.
--
--   Differences from the source:
--   - reading: 's sufficiently large in terms of α' → s ≥ s₀, with s₀ chosen together with r_α, c'_α and before L, X, s; reason: explicit form of 'sufficiently large'
--   - encoding: X ⊆ [0, L]_ℤ → L ∈ ℕ and X ⊆ Icc 0 L in ℤ; reason: [0, L]_ℤ = [0, ⌊L⌋]_ℤ and L^α ≥ ⌊L⌋^α, so the statement for real L ≥ 0 follows from the one for natural L
-- source:
--   Chen, Mao, Zhang (2026), An Almost-Linear Time Algorithm for Multidimensional Subset Sum, STOC 2027 submission, SHA-256 0cd42ca048cfff088013ad06450a278a6df72a29004c48c5c138f3f6df85d1e0, Theorem 9.A, p. 41

import Mathlib
import Definitions.Def_AlmostLinSubsetSum_Main_Basic
import Definitions.Def_AlmostLinSubsetSum_Main_GAP

set_option autoImplicit false

namespace AlmostLinSubsetSum.Main

/-- **Theorem 9.A** (Long sumsets; Conlon–Fox–Pham, cited in Chen, Mao, Zhang 2026, p. 41).
For every `α > 0` there are constants `r_α` and `c'_α > 0` such that: if `X ⊆ [0, L]_ℤ`
contains `0` and `s ≥ L^α` is an integer that is sufficiently large in terms of `α` (here:
`s ≥ s₀(α)`), then there is a centered GAP `P` of rank at most `r_α` containing `X` such that
`P_{c'_α s}` is proper and `z + P_{c'_α s} ⊆ sX` for some `z ∈ ℤ` (`sX` the `s`-fold sumset). -/
theorem theorem_9_A :
    ∀ α : ℝ, 0 < α →
    ∃ rα : ℕ, ∃ c' : ℝ, 0 < c' ∧ ∃ s₀ : ℕ,
    ∀ (L : ℕ) (X : Set ℤ), X ⊆ Set.Icc (0 : ℤ) L → (0 : ℤ) ∈ X →
    ∀ s : ℕ, s₀ ≤ s → (L : ℝ) ^ α ≤ (s : ℝ) →
      ∃ P : GAP, P.IsCentered ∧ P.rank ≤ rα ∧ X ⊆ P.carrier ∧
        P.IsDilateProper (c' * s) ∧
        ∃ z : ℤ, intTranslate z (P.dilateSet (c' * s)) ⊆ kFold s X := by sorry

end AlmostLinSubsetSum.Main
