-- Prove2me | Theorems.Thm_ExtremalForrelation_Nonadaptive_lemma_6
-- name    : ExtremalForrelation.Nonadaptive.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:24.876144+00:00
-- url     : https://prove2.me/theorems/d968ff5d-4e15-4486-953e-e51ffb21e5a4
-- title:
--   Lemma 6 — a uniform subspace is $r$-good with high probability
-- statement:
--   Throughout, $n$ is a multiple of $4$, $m=n/2$ and $M=2^m$ (the paper's standing notation, p. 3).
--
--   For every set $Q$ of $q$ queries and every integer $1\le r<m$, a uniformly random $m$-dimensional subspace $K$ is $r$-good for $Q$ with probability at least
--   $$1-2\binom{q}{r+2}M^{-(r+1)} .$$
--
--   This is the first term of (7).
--
--   Differences from the source: none.
-- source:
--   Clément Canonne, Kenny Chen, Julian Mestre, STOC 2027 submission #61 (October 2026), Lemma 6, p. 12, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/61.pdf

import Mathlib
import Definitions.Def_ExtremalForrelation_Nonadaptive_Pinning
import Definitions.Def_ExtremalForrelation_Nonadaptive_Algorithm

open Classical

namespace ExtremalForrelation.Nonadaptive

/-- Lemma 6 (p. 12). For every set `Q` of `q` queries and every integer `1 ≤ r < m`, a uniform
`m`-dimensional `K` is `r`-good with probability at least `1 − 2 binom(q, r+2) M^{−(r+1)}`. -/
theorem lemma_6 {n : ℕ} (hn : 4 ∣ n) (Q : Finset (V n)) (r : ℕ) (hr1 : 1 ≤ r) (hrm : r < n / 2) :
    1 - 2 * (Nat.choose Q.card (r + 2) : ℝ) * (((2 : ℝ) ^ (n / 2))⁻¹) ^ (r + 1) ≤
      uprob (fun K : Grass n => IsGood Q r K.1) := by sorry

end ExtremalForrelation.Nonadaptive
