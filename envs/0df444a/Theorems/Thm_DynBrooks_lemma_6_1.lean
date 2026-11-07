-- Prove2me | Theorems.Thm_DynBrooks_lemma_6_1
-- name    : DynBrooks.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:06:31.518194+00:00
-- url     : https://prove2.me/theorems/82480cdb-dd54-4bff-8069-969be76edf76
-- title:
--   Lemma 6.1 — the random walk reaches a free right vertex quickly
-- statement:
--   Fix any matching in a bipartite graph with at most $N$ left vertices, minimum left degree $\delta$ and maximum right degree $r<\delta$. From any specified unmatched left vertex, the random walk (select an incident right vertex uniformly; stop if it is free; otherwise move to its matched left vertex and repeat) reaches a free right vertex after a number $\tau$ of steps satisfying
--
--   $$P[\tau>s]\le\min\{1,\,N(r/\delta)^s\}\qquad(s\ge0).$$
--
--   In particular, when $r/\delta\le9/16$, the expected number of steps is $O(\log(N+1))$. For every fixed $c>0$, it finds an augmenting path within $O(\log(N+1)+\log n)$ steps with probability at least $1-n^{-c}$; erasing the loops of the stopped walk gives an augmenting path from the root. The constant of this last bound depends only on $c$ and on a fixed bound $\rho<1$ for $r/\delta$.
--
--   This is the matching repair of the constant-degree branch (§6.2).
--
--   Differences from the source:
--   - generalization: minimum left degree δ, maximum right degree r < δ → δ is any lower bound on the left degrees and r any upper bound on the right degrees, r < δ; reason: the minimum and the maximum are one such choice; the proof uses only the two bounds
--   - encoding: the expected number of steps → Σ_{s≥0} P[τ > s] in ℝ≥0∞; reason: the tail-sum formula is the expectation of an ℕ∞-valued variable
--   - reading: 'For every fixed c > 0, it finds an augmenting path within O(log(N+1) + log n) steps' → for every fixed c > 0 and every fixed bound ρ < 1 on r/δ, for every n ≥ 1, with a constant depending only on c and ρ; ρ = 9/16 is the case the paper uses; reason: the sentence states no hypothesis on r/δ, and the O-constant cannot be uniform as r/δ → 1; the proof takes s ≥ (log N + c log n)/log(1/ρ), which gives every such ρ
--   - encoding: finds an augmenting path → the walk stops within the bound with the stated probability, and the loop erasure of every stopped walk is an augmenting path from the root (for every matching and unmatched root, with no degree hypothesis); reason: the paper's proof obtains the path by loop erasure; the erasure argument uses only the matching
-- source:
--   Mishra, Mukherjee, Fully Dynamic Brooks Coloring (STOC 2027 submission, preprint, sha256 6542a9f18a48e0b539c2aadee984a641d38a01a551fd32d5fa4d4c5164e32d7b), Lemma 6.1, p.67 (PDF 69)

import Mathlib
import Definitions.Def_DynBrooks_MatchingWalk

open ENNReal

namespace DynBrooks

/-- **Lemma 6.1** (Mishra, Mukherjee, *Fully Dynamic Brooks Coloring*, STOC 2027 submission,
sha256 6542a9f1…, p.67 (PDF 69)). Fix any matching in a bipartite graph with at most `N` left vertices,
minimum left degree `δ`, and maximum right degree `r < δ`. From any specified unmatched left vertex, the
random walk (select an incident right vertex uniformly; stop if it is free, otherwise move to its matched
left vertex) reaches a free right vertex after a number `τ` of steps satisfying
`P[τ > s] ≤ min{1, N(r/δ)^s}` for `s ≥ 0`. In particular, when `r/δ ≤ 9/16`, the expected number of steps
is `O(log(N + 1))`. For every fixed `c > 0`, it finds an augmenting path within `O(log(N + 1) + log n)`
steps with probability at least `1 − n^{−c}`.

**Formalization Note.** `survive adj mate s x₀ = P[τ > s]` is computed from the walk's exact law. The
expectation of the `ℕ∞`-valued `τ` is `Σ_{s ≥ 0} P[τ > s]` (an `ℝ≥0∞`-valued sum). `δ` and `r` are a lower
bound on the left degrees and an upper bound on the right degrees; the minimum and the maximum are one
such choice. The constant of the second clause is absolute. In the third clause, for `n ≥ 1`, the constant
depends only on `c` and on a fixed bound `ρ < 1` for `r/δ` (it cannot be uniform as `r/δ → 1`; the proof
takes `s ≥ (log N + c log n)/log(1/ρ)`), and `ρ = 9/16` is the case the paper uses. "Finds an augmenting
path" is: the walk stops within the bound with the stated probability, and erasing the loops of every
stopped walk gives an augmenting path from the root (fourth clause). -/
theorem lemma_6_1 :
    (∀ {L R : Type} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
        (adj : L → Finset R) (mate : R → Option L) (N δ r : ℕ),
        IsMatching adj mate → Fintype.card L ≤ N → (∀ x, δ ≤ (adj x).card) →
        (∀ y, (Finset.univ.filter fun x => y ∈ adj x).card ≤ r) → r < δ →
        ∀ x₀ : L, (∀ y, mate y ≠ some x₀) → ∀ s : ℕ,
          survive adj mate s x₀ ≤ min 1 ((N : ℝ) * ((r : ℝ) / δ) ^ s)) ∧
    (∃ C : ℝ, ∀ {L R : Type} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
        (adj : L → Finset R) (mate : R → Option L) (N δ r : ℕ),
        IsMatching adj mate → Fintype.card L ≤ N → (∀ x, δ ≤ (adj x).card) →
        (∀ y, (Finset.univ.filter fun x => y ∈ adj x).card ≤ r) → r < δ →
        (r : ℝ) / δ ≤ 9 / 16 →
        ∀ x₀ : L, (∀ y, mate y ≠ some x₀) →
          ∑' s : ℕ, ENNReal.ofReal (survive adj mate s x₀) ≤
            ENNReal.ofReal (C * Real.log ((N : ℝ) + 1))) ∧
    (∀ c : ℝ, 0 < c → ∀ ρ : ℝ, ρ < 1 → ∃ C : ℝ, ∀ {L R : Type} [Fintype L] [Fintype R]
        [DecidableEq L] [DecidableEq R] (adj : L → Finset R) (mate : R → Option L) (N δ r n : ℕ),
        IsMatching adj mate → Fintype.card L ≤ N → (∀ x, δ ≤ (adj x).card) →
        (∀ y, (Finset.univ.filter fun x => y ∈ adj x).card ≤ r) → r < δ →
        (r : ℝ) / δ ≤ ρ → 1 ≤ n →
        ∀ x₀ : L, (∀ y, mate y ≠ some x₀) →
          survive adj mate ⌈C * (Real.log ((N : ℝ) + 1) + Real.log n)⌉₊ x₀ ≤
            (n : ℝ) ^ (-c)) ∧
    (∀ {L R : Type} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
        (adj : L → Finset R) (mate : R → Option L),
        IsMatching adj mate → ∀ x₀ : L, (∀ y, mate y ≠ some x₀) →
        ∀ ys : List R, IsStoppedWalk adj mate x₀ ys →
          IsAugmentingPath adj mate x₀ (eraseLoops ys).reverse) := by sorry

end DynBrooks
