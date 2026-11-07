-- Prove2me | Theorems.Thm_BddExp3SUM_eq_8_to_10
-- name    : BddExp3SUM.eq_8_to_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:59:59.789641+00:00
-- url     : https://prove2.me/theorems/38f08d3d-cb27-4762-a795-4e6152c5f16a
-- title:
--   (8)–(10): $\mathbb EF\le2L\sigma n^2/R$, $\mathbb E(Z_\pi-Z_0)\le2L\sigma n^2$, the good event has probability $\ge5/6$, and $Z_0\le n^2$
-- statement:
--   For a fixed subinstance with its certificate and uniform rows: the number of triples of exact sum-order $d$, for $d\mid e$, $d>1$, is less than $2s_dn^2$;
--
--   $$\mathbb EF\le\sum_{d\mid e,\ d>1}2s_dn^2d^{-\ell}\le2L\sigma n^2/R,$$
--
--   $$\mathbb E(Z_\pi-Z_0)\le D\,\mathbb EF\le2L\sigma n^2;$$
--
--   with probability at least $5/6$ both
--
--   $$F\le24L\sigma n^2/R,\qquad Z_\pi-Z_0\le24L\sigma n^2$$
--
--   hold; and $Z_0\le n^2$.
--
--   These bounds hold for all divisors at once because of (2), and they drive both the probe count and the scan cap.
--
--   **Formalization Note** $Z_\pi-Z_0$ is a difference of real numbers; it is nonnegative because a true zero sum lies in $\ker\pi$.
--
--   Differences from the source:
--   - encoding: probability and expectation over independent uniform rows → counting ratios on Fin (k+q) → G; reason: the uniform law on a finite set
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Truly Subquadratic 3SUM over Every Bounded-Exponent Abelian Group, STOC 2027 submission (manuscript sha256 19546c9a…), (8)–(10), p.4 (PDF p.5)

import Mathlib
import Definitions.Def_BddExp3SUM_Hash

namespace BddExp3SUM

/-- (8), (9), (10) and `Z₀ ≤ n²`, p.4 (Zeng, Wang, Cao, Dai, Wang, STOC 2027 submission, manuscript
sha256 19546c9a…), for a fixed subinstance with its certificate and uniform rows
`u : Fin (k + q) → G`.

**Formalization Note.** `Z_π - Z₀` is a difference of real numbers. It is nonnegative, since a true
zero sum lies in `ker π`. -/
theorem eq_8_to_10 {M r n k q e p : ℕ} [NeZero M] {S U : Fin 3 → Finset (Grp M r)}
    (h : Cert M r n S U k q e p) :
    (∀ d ∈ Nat.divisors e, 1 < d → (countOrder U d : ℝ) < 2 * sMin S U d * (n : ℝ) ^ 2) ∧
    uniformExp (fun u : Fin (k + q) → Grp M r => (countFalse U (KHash e u) : ℝ)) ≤
      ∑ d ∈ (Nat.divisors e).filter (fun d => 1 < d),
        2 * (sMin S U d : ℝ) * (n : ℝ) ^ 2 * ((d : ℝ) ^ (k + q))⁻¹ ∧
    ∑ d ∈ (Nat.divisors e).filter (fun d => 1 < d),
        2 * (sMin S U d : ℝ) * (n : ℝ) ^ 2 * ((d : ℝ) ^ (k + q))⁻¹ ≤
      2 * Lcard M * σ M n * (n : ℝ) ^ 2 / R M n ∧
    uniformExp (fun u : Fin (k + q) → Grp M r =>
        (countKer U (piHash h.p_dvd e u) : ℝ) - countZero U) ≤
      (p : ℝ) ^ q * uniformExp (fun u : Fin (k + q) → Grp M r => (countFalse U (KHash e u) : ℝ)) ∧
    (p : ℝ) ^ q * uniformExp (fun u : Fin (k + q) → Grp M r => (countFalse U (KHash e u) : ℝ)) ≤
      2 * Lcard M * σ M n * (n : ℝ) ^ 2 ∧
    5 / 6 ≤ uniformProb (fun u : Fin (k + q) → Grp M r =>
      GoodEvent n U (piHash h.p_dvd e u) (KHash e u)) ∧
    (countZero U : ℝ) ≤ (n : ℝ) ^ 2 := by sorry

end BddExp3SUM
