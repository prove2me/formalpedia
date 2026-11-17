-- Prove2me | Theorems.Thm_ErrAmpOV_Supplement_theorem_3_3
-- name    : ErrAmpOV.Supplement.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:17:20.603584+00:00
-- url     : https://prove2.me/theorems/2f576c55-0e04-48b1-8e7b-25b66458af6b
-- title:
--   Theorem 3.3 — the zero-error and deterministic OV conjectures are equivalent (both versions)
-- statement:
--   Write $\mathrm{OV}_{n,d}$ for the Orthogonal Vectors problem on two lists of $n$ vectors in $\{0,1\}^d$, $\mathrm{SIZE}[S]$ for deterministic circuits of size at most $S$, and $\mathrm{ZPSIZE}_{1/10}[S]$ for zero-error probabilistic circuits of size at most $S$ that answer correctly with probability at least $9/10$ and otherwise output $\bot$. A dimension function $d:\mathbb N\to\mathbb N$ is in the **low-dimensional regime** when $d(n)=\omega(\log n)$ and $d(n)=n^{o(1)}$.
--
--   1. **(Infinitely many $n$.)** Suppose that for every low-dimensional $d$ and every constant $0<\alpha<1$,
--   $$\mathrm{OV}_{n,d(n)}\notin\mathrm{SIZE}\bigl[n^{2-\alpha}\bigr]\quad\text{for infinitely many } n .$$
--   Then for every low-dimensional $d$ and every $0<\alpha<1$, $\mathrm{OV}_{n,d(n)}\notin\mathrm{ZPSIZE}_{1/10}[n^{2-\alpha}]$ for infinitely many $n$.
--   2. **(Almost every $n$.)** The same statement with "for infinitely many $n$" replaced by "for all sufficiently large $n$", in the hypothesis and in the conclusion.
--
--   So the OV conjecture for deterministic circuits implies the same conjecture for zero-error probabilistic circuits, in both its infinitely-often and its almost-everywhere forms; the converse is immediate.
--
--   **Formalization Note** Sizes $n^{2-\alpha}$ are exact real powers, with no hidden constant; the error is exactly $1/10$.
--
--   Differences from the source:
--   - reading: for infinitely many (almost every) n, all d := d(n) between ω(log n) and n^{o(1)}, and any constant 0 < α < 1 → for every dimension function d with LowDim d and every 0 < α < 1, ∃ᶠ n (resp. ∀ᶠ n) in atTop; reason: a dimension function has no regime at a single n, so d and α are quantified first and the infinite set (threshold) of n may depend on them; the published base items use the same reading (R2)
--   - encoding: Boolean circuits with no fixed gate basis; SIZE and ZPSIZE with sizes written without O(·) → ErrAmpOV.Circuit (constants, NOT, AND, OR, fan-in ≤ 2), sizes exact, ⊥ as a first output wire set to true with the remaining output wire left free (p.5 pads ⊥ with zeros); reason: the published base model; the page writes no O(·), so sizes are exact as in the base mission; the ⊥ padding is a presentation convention of p.5 (the base ZPDecides leaves it free)
-- source:
--   Koucký, Mertz, Rajgopal, Efficient Error Amplification for Sorting and Orthogonal Vectors, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3), Theorem 3.3, p.12

import Mathlib
import Definitions.Def_ErrAmpOV_SizeDecides
import Definitions.Def_ErrAmpOV_ZPDecides
import Definitions.Def_ErrAmpOV_OV
import Definitions.Def_ErrAmpOV_LowDim

set_option autoImplicit false

namespace ErrAmpOV.Supplement

/-- Theorem 3.3 (Equivalence of zero-error and deterministic conjectures for OV), p.12, in both
printed versions.

1. (Infinitely many `n`.) Suppose that for every dimension function `d` with
   `ω(log n) ≤ d(n) ≤ n^{o(1)}` and every constant `0 < α < 1`, for infinitely many `n`,
   `OV_{n,d(n)}` has no deterministic circuit of size at most `n^{2−α}`. Then for every such `d`
   and every `0 < α < 1`, for infinitely many `n`, `OV_{n,d(n)}` has no zero-error probabilistic
   circuit of size at most `n^{2−α}` with error at most `1/10`.
2. (Almost every `n`.) The same with "for infinitely many `n`" replaced by "for all
   sufficiently large `n`", in the hypothesis and in the conclusion.

Source: Koucký, Mertz, Rajgopal, *Efficient Error Amplification for Sorting and Orthogonal
Vectors*, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3),
Theorem 3.3, p.12.

**Formalization Note.**
* "For infinitely many (almost every) `n`, all `d := d(n)` between `ω(log n)` and `n^{o(1)}`,
  and any constant `0 < α < 1`" is `∀ d, LowDim d → ∀ α, 0 < α → α < 1 → ∃ᶠ n in atTop, …`
  (resp. `∀ᶠ n in atTop`): a dimension function has no regime at one fixed `n` (base reading
  R2). The two printed versions are the two conjuncts, with the same quantifier on both sides.
* Sizes `n^{2−α}` are exact (`Real.rpow`, no `O`-constant, no `d^c` factor); error `1/10`. -/
theorem theorem_3_3 :
    ((∀ d : ℕ → ℕ, ErrAmpOV.LowDim d → ∀ α : ℝ, 0 < α → α < 1 →
        ∃ᶠ n : ℕ in Filter.atTop,
          ¬ ErrAmpOV.SizeDecides ((n : ℝ) ^ (2 - α)) (ErrAmpOV.OV n (d n))) →
      ∀ d : ℕ → ℕ, ErrAmpOV.LowDim d → ∀ α : ℝ, 0 < α → α < 1 →
        ∃ᶠ n : ℕ in Filter.atTop,
          ¬ ErrAmpOV.ZPDecides (1 / 10) ((n : ℝ) ^ (2 - α)) (ErrAmpOV.OV n (d n))) ∧
    ((∀ d : ℕ → ℕ, ErrAmpOV.LowDim d → ∀ α : ℝ, 0 < α → α < 1 →
        ∀ᶠ n : ℕ in Filter.atTop,
          ¬ ErrAmpOV.SizeDecides ((n : ℝ) ^ (2 - α)) (ErrAmpOV.OV n (d n))) →
      ∀ d : ℕ → ℕ, ErrAmpOV.LowDim d → ∀ α : ℝ, 0 < α → α < 1 →
        ∀ᶠ n : ℕ in Filter.atTop,
          ¬ ErrAmpOV.ZPDecides (1 / 10) ((n : ℝ) ^ (2 - α)) (ErrAmpOV.OV n (d n))) := by sorry

end ErrAmpOV.Supplement
