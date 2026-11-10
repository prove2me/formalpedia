-- Prove2me | Theorems.Thm_DetParamSVP_eq_3_from_eq_12
-- name    : DetParamSVP.eq_3_from_eq_12
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T10:51:45.434448+00:00
-- url     : https://prove2.me/theorems/7b26a96a-c5fd-4dd4-b011-fb988d2aef66
-- title:
--   Proof of Theorem 3.5 — Eq. (12) gives the hypotheses (6) and Eq. (3)
-- statement:
--   Let $p\ge1$, let $\gamma\ge2$ and $c\ge1$ be integers with $\gamma^p/2+8\le c^p$, let $d\ge1$, put $D=\gamma d$, and let $h,k$ be integers with
--
--   $$d^p\le h<d^p+\tfrac32,\qquad D^p/2<k<D^p/2+\tfrac32.\tag{12}$$
--
--   Then $D\ge2$, $k\ge2$, $D^p<2k$ and $d^p\le h$ (the hypotheses (6) of Theorem 3.4), and with $W=k-1+2h$,
--
--   $$d^p+W+1<\tfrac{D^p}2+3d^p+\tfrac92\le\Big(\tfrac{\gamma^p}2+8\Big)d^p\le(cd)^p,$$
--
--   so Eq. (3) of Theorem 3.2 holds.
--
--   This is the parameter check that lets Theorems 3.2 and 3.4 be combined.
--
--   Differences from the source:
--   - encoding: W = k − 1 + 2h, D = γd → the real number (k:ℝ) − 1 + 2h; the natural number γ·d; reason: same values
--   - generalization: all of Eq. (11) (including γ′c < γ) → only γ ≥ 2, c ≥ 1 and γ^p/2 + 8 ≤ c^p; reason: γ′c < γ is not used in this step; the source parameters satisfy the hypotheses
-- source:
--   Hirahara–Lin–Liu–Ogitsuka, Deterministic Parameterized Inapproximability of the Shortest Vector and Minimum Distance Problems, STOC 2027 submission (manuscript sha256 4584f5e2…), proof of Theorem 3.5, Eq. (12), p.23, and p.24

import Mathlib

set_option autoImplicit false

namespace DetParamSVP

/-- **Proof of Theorem 3.5: Eq. (3) from Eq. (12).** Let `p ≥ 1`, let `γ ≥ 2` and `c ≥ 1` be
integers with `γ^p/2 + 8 ≤ c^p` (from (11)), let `d ≥ 1`, `D = γd`, and let `h, k` be integers with
`d^p ≤ h < d^p + 3/2` and `D^p/2 < k < D^p/2 + 3/2` (12). Then the hypotheses (6) of Theorem 3.4
hold (`D ≥ 2`, `k ≥ 2`, `D^p < 2k`, `d^p ≤ h`), and with `W = k − 1 + 2h`,
`d^p + W + 1 < D^p/2 + 3d^p + 9/2 ≤ (γ^p/2 + 8)d^p ≤ (cd)^p`.

Hirahara–Lin–Liu–Ogitsuka, *Deterministic Parameterized Inapproximability of the Shortest Vector
and Minimum Distance Problems*, STOC 2027 submission (manuscript sha256 4584f5e2…), proof of Theorem 3.5, Eq. (12), p.23, and p.24.

**Formalization Note.** `D = γd` is written out as the natural number `γ * d`; all real
comparisons use casts and `Real.rpow`. `W = k − 1 + 2h` is the real number `(k:ℝ) − 1 + 2h`. Each
link of the chain is a separate conclusion. -/
theorem eq_3_from_eq_12 (p : ℝ) (hp : 1 ≤ p) (γ c d h k : ℕ) (hγ : 2 ≤ γ) (hc : 1 ≤ c)
    (hγc : (γ : ℝ) ^ p / 2 + 8 ≤ (c : ℝ) ^ p) (hd : 1 ≤ d)
    (hh₁ : (d : ℝ) ^ p ≤ h) (hh₂ : (h : ℝ) < (d : ℝ) ^ p + 3 / 2)
    (hk₁ : ((γ * d : ℕ) : ℝ) ^ p / 2 < k) (hk₂ : (k : ℝ) < ((γ * d : ℕ) : ℝ) ^ p / 2 + 3 / 2) :
    2 ≤ γ * d ∧ 2 ≤ k ∧ ((γ * d : ℕ) : ℝ) ^ p < 2 * k ∧ (d : ℝ) ^ p ≤ h ∧
      (d : ℝ) ^ p + ((k : ℝ) - 1 + 2 * h) + 1 < ((γ * d : ℕ) : ℝ) ^ p / 2 + 3 * (d : ℝ) ^ p + 9 / 2 ∧
      ((γ * d : ℕ) : ℝ) ^ p / 2 + 3 * (d : ℝ) ^ p + 9 / 2 ≤ ((γ : ℝ) ^ p / 2 + 8) * (d : ℝ) ^ p ∧
      ((γ : ℝ) ^ p / 2 + 8) * (d : ℝ) ^ p ≤ ((c * d : ℕ) : ℝ) ^ p := by sorry

end DetParamSVP
