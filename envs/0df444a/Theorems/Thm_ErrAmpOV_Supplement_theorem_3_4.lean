-- Prove2me | Theorems.Thm_ErrAmpOV_Supplement_theorem_3_4
-- name    : ErrAmpOV.Supplement.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:17:51.85371+00:00
-- url     : https://prove2.me/theorems/73ca6b2b-1dd6-4bf2-8497-f9d1c94e68eb
-- title:
--   Theorem 3.4 — zero-error circuits of size $n^{k-\alpha}d^c$ for low-dimensional $k$-OV give deterministic circuits of size $n^{k-\alpha/4}d^c$
-- statement:
--   Write $k\text{-}\mathrm{OV}_{n,d}$ for the $k$-partite Orthogonal Vectors problem: given $k$ lists of $n$ vectors in $\{0,1\}^d$, decide whether one vector $a_j$ can be chosen from each list $j$ with $\sum_{l}\prod_{j}a_j[l]=0$. A dimension function $d$ is low-dimensional when $d(n)=\omega(\log n)$ and $d(n)=n^{o(1)}$.
--
--   Let $k\in\mathbb N$, $0<\alpha<1$ and $c\in\mathbb N$. Suppose that for every low-dimensional $d$, for all sufficiently large $n$,
--   $$k\text{-}\mathrm{OV}_{n,d(n)}\in\mathrm{ZPSIZE}_{1/10}\bigl[n^{k-\alpha}\cdot d(n)^c\bigr].$$
--   Then for every low-dimensional $d$, for all sufficiently large $n$,
--   $$k\text{-}\mathrm{OV}_{n,d(n)}\in\mathrm{SIZE}\bigl[n^{k-\alpha/4}\cdot d(n)^c\bigr].$$
--
--   This extends the mission's goal (the case $k=2$) to every $k$: a polynomial saving over brute force for zero-error circuits yields a polynomial saving for deterministic circuits.
--
--   **Formalization Note** Sizes are exact on both sides; $\alpha$ and $c$ are the same in hypothesis and conclusion; $k$ ranges over all natural numbers, as on the page.
--
--   Differences from the source:
--   - reading: for all sufficiently large n and all d := d(n) between ω(log n) and n^{o(1)} → for every dimension function d with LowDim d, ∀ᶠ n in atTop (threshold may depend on d), in hypothesis and conclusion; reason: a dimension function has no regime at one n; same reading as the published goal Theorem 3.1 (R2)
--   - encoding: Boolean circuits with no fixed gate basis; SIZE and ZPSIZE with sizes written without O(·) → ErrAmpOV.Circuit (constants, NOT, AND, OR, fan-in ≤ 2), sizes exact, ⊥ as a first output wire set to true with the remaining output wire left free (p.5 pads ⊥ with zeros); reason: the published base model; the page writes no O(·), so sizes are exact as in the base mission; the ⊥ padding is a presentation convention of p.5 (the base ZPDecides leaves it free)
-- source:
--   Koucký, Mertz, Rajgopal, Efficient Error Amplification for Sorting and Orthogonal Vectors, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3), Theorem 3.4, p.12 (informal version Theorem 1.2, p.2)

import Mathlib
import Definitions.Def_ErrAmpOV_SizeDecides
import Definitions.Def_ErrAmpOV_ZPDecides
import Definitions.Def_ErrAmpOV_kOV
import Definitions.Def_ErrAmpOV_LowDim

set_option autoImplicit false

namespace ErrAmpOV.Supplement

/-- Theorem 3.4 (Efficient derandomization of zero-error probabilistic circuits for
low-dimensional `k`-OV), p.12; formal version of Theorem 1.2, p.2. Let `k ∈ ℕ`, `0 < α < 1`
and `c ∈ ℕ`. Suppose that for every dimension function `d` with `ω(log n) ≤ d(n) ≤ n^{o(1)}`,
for all sufficiently large `n`, `k-OV_{n,d(n)}` has zero-error probabilistic circuits of size at
most `n^{k−α}·d(n)^c` with error at most `1/10`. Then for every such `d`, for all sufficiently
large `n`, `k-OV_{n,d(n)}` has deterministic circuits of size at most `n^{k−α/4}·d(n)^c`.

Source: Koucký, Mertz, Rajgopal, *Efficient Error Amplification for Sorting and Orthogonal
Vectors*, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3),
Theorem 3.4, p.12.

**Formalization Note.**
* Same shape as the published `ErrAmpOV.theorem_3_1` with `2` replaced by `k`: the regime is
  `∀ d, LowDim d → ∀ᶠ n in atTop, …` on both sides; sizes are exact; `α` and `c` are the same
  in hypothesis and conclusion; `n^{k−α}`, `n^{k−α/4}` are `Real.rpow` with `(k : ℝ)`, `d(n)^c`
  a natural power.
* `k` ranges over all of `ℕ` ("Let `k ∈ N`"); `k = 0, 1` are degenerate cases of the same
  statement. -/
theorem theorem_3_4 (k : ℕ) (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1) (c : ℕ)
    (h : ∀ d : ℕ → ℕ, ErrAmpOV.LowDim d → ∀ᶠ n : ℕ in Filter.atTop,
      ErrAmpOV.ZPDecides (1 / 10) ((n : ℝ) ^ ((k : ℝ) - α) * (d n : ℝ) ^ c)
        (ErrAmpOV.kOV k n (d n))) :
    ∀ d : ℕ → ℕ, ErrAmpOV.LowDim d → ∀ᶠ n : ℕ in Filter.atTop,
      ErrAmpOV.SizeDecides ((n : ℝ) ^ ((k : ℝ) - α / 4) * (d n : ℝ) ^ c)
        (ErrAmpOV.kOV k n (d n)) := by sorry

end ErrAmpOV.Supplement
