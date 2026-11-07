-- Prove2me | Theorems.Thm_ApproxDegComp_lemma_7
-- name    : ApproxDegComp.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:31:42.470917+00:00
-- url     : https://prove2.me/theorems/605051b3-27e3-4d82-b04d-b6469807263e
-- title:
--   Lemma 7 — homogeneous Taylor parts of a bounded trigonometric polynomial: $|H_0|\le1$, $\|H_r\|_{[-1,1]^n}\le(eD/r)^r$
-- statement:
--   Let $R:\mathbb R^n\to\mathbb C$ be a trigonometric polynomial of total frequency at most $D$ with $|R(\theta)|\le1$ for all $\theta\in\mathbb R^n$, and write its Taylor expansion at zero as $R=\sum_{r\ge0}H_r$ with $H_r$ homogeneous of degree $r$. Then $|H_0|\le1$ and, for every $r\ge1$,
--
--   $$\|H_r\|_{[-1,1]^n}\le\Bigl(\frac{eD}r\Bigr)^r.$$
--
--   This is a Bernstein-type bound; together with Lemma 6 it controls the high-degree part of the squarefree extraction in the proof of Theorem 23.
--
--   **Formalization Note** $H_r(y)$ is the $r$-th Taylor coefficient of $s\mapsto R(sy)$; the sup norm is a bound at every $y\in[-1,1]^n$. $D$ is a natural number.
--
--   Differences from the source:
--   - encoding: total frequency at most D → D a natural number; reason: total frequency is an integer ℓ₁ norm, so "at most D" for real D ≥ 0 means at most ⌊D⌋, and (e⌊D⌋/r)^r ≤ (eD/r)^r
--   - encoding: ‖H_r‖_{[−1,1]ⁿ} ≤ (eD/r)^r → |H_r(y)| ≤ (eD/r)^r for every y ∈ [−1,1]ⁿ; reason: the definition of the sup norm
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Lemma 7, p.16 (proof Appendix A, pp.42–43)

import Mathlib
import Definitions.Def_ApproxDegComp_HasTotalFreqLE
import Definitions.Def_ApproxDegComp_taylorHom

namespace ApproxDegComp

/-- **Lemma 7 (Homogeneous Taylor coefficients)**, p.16 (proof in Appendix A, pp.42–43).
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Lemma 7, p.16: "Suppose R is a trigonometric polynomial of total frequency at most D and
|R(θ)| ≤ 1 for all θ ∈ ℝⁿ. Taking Taylor expansion at zero as R = Σ_{r≥0} H_r, where H_r is
homogeneous of degree r. Then |H₀| ≤ 1 and for r ≥ 1, ‖H_r‖_{[−1,1]ⁿ} ≤ (eD/r)^r."

**Formalization Note** `R` is complex-valued, as Definitions 18 and 21 allow; `H_r = taylorHom R r`.
The sup norm on `[−1,1]ⁿ` is a pointwise bound for every `y` in the cube `[−1,1]ⁿ`. -/
theorem lemma_7 (n D : ℕ) (R : (Fin n → ℝ) → ℂ) (hR : HasTotalFreqLE R D)
    (hb : ∀ θ, ‖R θ‖ ≤ 1) :
    (∀ y, ‖taylorHom R 0 y‖ ≤ 1) ∧
      ∀ r : ℕ, 1 ≤ r → ∀ y : Fin n → ℝ, (∀ i, |y i| ≤ 1) →
        ‖taylorHom R r y‖ ≤ (Real.exp 1 * (D : ℝ) / (r : ℝ)) ^ r := by sorry

end ApproxDegComp
