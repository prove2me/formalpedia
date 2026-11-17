-- Prove2me | Theorems.Thm_ErrAmpOV_Supplement_theorem_3_5
-- name    : ErrAmpOV.Supplement.theorem_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:18:29.395696+00:00
-- url     : https://prove2.me/theorems/ab59f95b-805b-40b0-8502-90b135bd8467
-- title:
--   Theorem 3.5 — the zero-error and deterministic $k$-OV conjectures are equivalent (both versions)
-- statement:
--   With the notation of Theorem 3.3 and $k\text{-}\mathrm{OV}_{n,d}$ the $k$-partite Orthogonal Vectors problem, let $k\in\mathbb N$.
--
--   1. **(Infinitely many $n$.)** Suppose that for every low-dimensional $d$ and every constant $0<\alpha<1$,
--   $$k\text{-}\mathrm{OV}_{n,d(n)}\notin\mathrm{SIZE}\bigl[n^{k-\alpha}\bigr]\quad\text{for infinitely many } n .$$
--   Then for every low-dimensional $d$ and every $0<\alpha<1$, $k\text{-}\mathrm{OV}_{n,d(n)}\notin\mathrm{ZPSIZE}_{1/10}[n^{k-\alpha}]$ for infinitely many $n$.
--   2. **(Almost every $n$.)** The same statement with "for infinitely many $n$" replaced by "for all sufficiently large $n$", in the hypothesis and in the conclusion.
--
--   This is the $k$-partite form of the equivalence of the deterministic and zero-error OV conjectures.
--
--   **Formalization Note** Sizes $n^{k-\alpha}$ are exact real powers; the error is exactly $1/10$; $k$ ranges over all natural numbers.
--
--   Differences from the source:
--   - reading: for infinitely many (almost every) n, all d := d(n) between ω(log n) and n^{o(1)}, and any constant 0 < α < 1 → for every dimension function d with LowDim d and every 0 < α < 1, ∃ᶠ n (resp. ∀ᶠ n) in atTop; reason: a dimension function has no regime at a single n, so d and α are quantified first and the infinite set (threshold) of n may depend on them; the published base items use the same reading (R2)
--   - encoding: Boolean circuits with no fixed gate basis; SIZE and ZPSIZE with sizes written without O(·) → ErrAmpOV.Circuit (constants, NOT, AND, OR, fan-in ≤ 2), sizes exact, ⊥ as a first output wire set to true with the remaining output wire left free (p.5 pads ⊥ with zeros); reason: the published base model; the page writes no O(·), so sizes are exact as in the base mission; the ⊥ padding is a presentation convention of p.5 (the base ZPDecides leaves it free)
-- source:
--   Koucký, Mertz, Rajgopal, Efficient Error Amplification for Sorting and Orthogonal Vectors, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3), Theorem 3.5, p.12

import Mathlib
import Definitions.Def_ErrAmpOV_SizeDecides
import Definitions.Def_ErrAmpOV_ZPDecides
import Definitions.Def_ErrAmpOV_kOV
import Definitions.Def_ErrAmpOV_LowDim

set_option autoImplicit false

namespace ErrAmpOV.Supplement

/-- Theorem 3.5 (Equivalence of zero-error and deterministic conjectures for `k`-OV), p.12, in
both printed versions. Let `k ∈ ℕ`.

1. (Infinitely many `n`.) Suppose that for every dimension function `d` with
   `ω(log n) ≤ d(n) ≤ n^{o(1)}` and every constant `0 < α < 1`, for infinitely many `n`,
   `k-OV_{n,d(n)}` has no deterministic circuit of size at most `n^{k−α}`. Then for every such
   `d` and every `0 < α < 1`, for infinitely many `n`, `k-OV_{n,d(n)}` has no zero-error
   probabilistic circuit of size at most `n^{k−α}` with error at most `1/10`.
2. (Almost every `n`.) The same with "for infinitely many `n`" replaced by "for all
   sufficiently large `n`", in the hypothesis and in the conclusion.

Source: Koucký, Mertz, Rajgopal, *Efficient Error Amplification for Sorting and Orthogonal
Vectors*, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3),
Theorem 3.5, p.12.

**Formalization Note.** As for Theorem 3.3: `∀ d, LowDim d → ∀ α ∈ (0,1) → ∃ᶠ n` (resp. `∀ᶠ n`),
the same quantifier on both sides, the two versions as two conjuncts; sizes `n^{k−α}` exact
(`Real.rpow` with `(k : ℝ)`), error `1/10`; `k` ranges over all of `ℕ`. -/
theorem theorem_3_5 (k : ℕ) :
    ((∀ d : ℕ → ℕ, ErrAmpOV.LowDim d → ∀ α : ℝ, 0 < α → α < 1 →
        ∃ᶠ n : ℕ in Filter.atTop,
          ¬ ErrAmpOV.SizeDecides ((n : ℝ) ^ ((k : ℝ) - α)) (ErrAmpOV.kOV k n (d n))) →
      ∀ d : ℕ → ℕ, ErrAmpOV.LowDim d → ∀ α : ℝ, 0 < α → α < 1 →
        ∃ᶠ n : ℕ in Filter.atTop,
          ¬ ErrAmpOV.ZPDecides (1 / 10) ((n : ℝ) ^ ((k : ℝ) - α)) (ErrAmpOV.kOV k n (d n))) ∧
    ((∀ d : ℕ → ℕ, ErrAmpOV.LowDim d → ∀ α : ℝ, 0 < α → α < 1 →
        ∀ᶠ n : ℕ in Filter.atTop,
          ¬ ErrAmpOV.SizeDecides ((n : ℝ) ^ ((k : ℝ) - α)) (ErrAmpOV.kOV k n (d n))) →
      ∀ d : ℕ → ℕ, ErrAmpOV.LowDim d → ∀ α : ℝ, 0 < α → α < 1 →
        ∀ᶠ n : ℕ in Filter.atTop,
          ¬ ErrAmpOV.ZPDecides (1 / 10) ((n : ℝ) ^ ((k : ℝ) - α)) (ErrAmpOV.kOV k n (d n))) := by sorry

end ErrAmpOV.Supplement
