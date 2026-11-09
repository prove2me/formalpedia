-- Prove2me | Theorems.Thm_DeMorganApprox_Main_lemma_5_9
-- name    : DeMorganApprox.Main.lemma_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:02:35.182204+00:00
-- url     : https://prove2.me/theorems/455c2027-c0fa-4b5e-9f4f-75f26f770cbc
-- title:
--   Lemma 5.9 — the full available-vector matrix of the constructed program has ‖abs(V)‖ = O(1)
-- statement:
--   Let $V$ be the full available-vector matrix of the span program constructed for a De Morgan formula, with all its listed vectors (literal, rotation and connector vectors) as columns. Then
--   $$\|\operatorname{abs}(V)\|=O(1),$$
--   with one absolute constant, independent of the formula, the number of variables and the tie rule.
--
--   Together with Lemma 5.7 this provides both hypotheses of the extraction lemma (Lemma 4.1).
--
--   Differences from the source:
--   - reading: ‖abs(V)‖ = O(1) → ∃ c chosen before m, the tie rule and the formula T, with AbsNormLE (program tie T).vec c; reason: O(1) is one absolute constant; the proof gives c² = 2 + 4·4²
--   - generalization: the span program of a formula with n ≥ 2 leaves (the proof of Theorem 5.1 treats n = 1 separately) → every formula T, including a single leaf, whose program is the leaf program of Lemma 5.2; reason: the one-leaf program has one unit column; the statement specializes to the source's case
--   - encoding: a heavy-chain decomposition with ties broken arbitrarily → ∀ tie : List Bool → Bool, a tie choice for every node; reason: the source allows either child at a tie (PDF p. 20)
--   - encoding: a real Euclidean space H with unit vectors and the entrywise absolute value abs(V) → the coordinate space ι → ℝ for a finite type ι with its standard basis; squared norms are sums of squares; reason: abs(V) is only defined relative to a fixed orthonormal basis, which the construction provides (leaf and helper coordinates); finitely many listed vectors span a finite-dimensional subspace
-- source:
--   Yichuan Wang, STOC 2027 submission #76 (October 2026), Lemma 5.9, PDF p. 27 (printed p. 25), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/76.pdf; proof PDF pp. 27–28 (printed pp. 25–26)

import Mathlib
import Definitions.Def_DeMorganApprox_Main_HeavyChains

namespace DeMorganApprox.Main

/-- Lemma 5.9, PDF p. 27 (printed p. 25); proof PDF pp. 27–28. One absolute constant `c` for
the full available-vector matrix of every constructed program. -/
theorem lemma_5_9 :
    ∃ c : ℝ, ∀ (m : ℕ) (tie : TieRule) (T : Formula m), AbsNormLE (program tie T).vec c
    := by sorry

end DeMorganApprox.Main
