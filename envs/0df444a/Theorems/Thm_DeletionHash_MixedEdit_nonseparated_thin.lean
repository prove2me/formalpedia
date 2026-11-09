-- Prove2me | Theorems.Thm_DeletionHash_MixedEdit_nonseparated_thin
-- name    : DeletionHash.MixedEdit.nonseparated_thin
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:20.406121+00:00
-- url     : https://prove2.me/theorems/75b41929-8a91-404a-acfc-02061a369456
-- title:
--   Lemma 3.4 — nonseparated thin
-- statement:
--   For every $t\ge2$ and $b\ge1$, there is a positive constant $c_{t,b}$ independent of alphabet size. For every alphabet of size $q\ge2$, every $n,k,L$ in the standing proof regime, every $r\ge1$ and each $x\in W_{n,k}$,
--   $$\Pr_H[x\in E]\le c_{t,b}\,q^{2bt}L n^{2t-1}/2^r.$$
--   Here $E$ is computed from actual short or nonseparated equal-label records and may contain partners that are not unique. The same constant works for all alphabets, lengths and label dimensions. This bounds the first exceptional family discarded in code selection.
--
--   Differences from the source:
--   - encoding: the standing assumptions of §§2.2–6 → Regime: q≥2, t≥2, b≥1, k=2 ceil(log_q n)+2, L=3(k+b+1), b<k, L≤n; reason: the section preamble is explicit in each applicable signature
--   - encoding: a constant c depending only on t,b → a positive real c before q, alphabet, length and r; reason: a nonnegative upper-bound constant may be increased to a positive one without changing any instance
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), Lemma 3.4, printed p. 10 (PDF p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Definitions.Def_DeletionHash_MixedEdit_ConflictGraph

namespace DeletionHash.MixedEdit

universe u

/-- Lemma 3.4: c precedes every alphabet, length and label dimension. -/
theorem nonseparated_thin (t b : ℕ) (ht : 2 ≤ t) (hb : 1 ≤ b) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) (α : Type u) [Fintype α] [DecidableEq α],
      Fintype.card α = q → ∀ n k L r : ℕ, Regime q n t b k L → 1 ≤ r →
      ∀ x : Word α n, IsUnique k (letters x) →
      uniformProbability (fun ξ : HashSample α L r => Exceptional n k t b ξ x) ≤
        c * (q : ℝ)^(2*b*t) * (L : ℝ) * (n : ℝ)^(2*t-1) / (2 : ℝ)^r := by sorry

end DeletionHash.MixedEdit
