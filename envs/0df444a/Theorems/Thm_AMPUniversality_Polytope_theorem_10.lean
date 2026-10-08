-- Prove2me | Theorems.Thm_AMPUniversality_Polytope_theorem_10
-- name    : AMPUniversality.Polytope.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:37:36.85259+00:00
-- url     : https://prove2.me/theorems/9aa0bf3b-c2f8-4996-91f1-4ffe55ae8a10
-- title:
--   Theorem 10, p. 70 — smoothed bound P{σ_N(B + νG) ≤ νz} ≤ (a₁z)^(M−N+1) for Gaussian perturbations
-- statement:
--   Fix $a>0$. There are constants $a_1,a_2>0$, depending only on $a$, with the following property. Let $M,N\in\mathbb N$ with $N\le(1-a)M$, let $B\in\mathbb R^{M\times N}$ be a deterministic matrix with operator norm $\|B\|_2\le 1/a$, let $G\in\mathbb R^{M\times N}$ have i.i.d. entries $G_{ij}\sim\mathsf N(0,1/M)$, and let $\nu>0$. Then for every $z\in(0,a_2)$,
--
--   $$\mathbb P\{\sigma_N(B+\nu G)\le\nu z\}\le(a_1z)^{M-N+1},$$
--
--   where $\sigma_N(\cdot)$ is the $N$-th (smallest) singular value of an $M\times N$ matrix.
--
--   The bound controls the restricted singular values of the Gaussian-perturbed sensing matrix, which is how the Gaussian component $\nu_0G$ of Theorems 2 and 8 is used. The result is cited from Bürgisser and Cucker, Theorem 1.1.
--
--   **Formalization Note** The page writes $\sigma_N(A+\nu G)$ while the hypothesis names the deterministic matrix $B$; the statement uses $B$. The page leaves $\nu$ unquantified; the statement takes $\nu>0$, uniformly, and $z>0$ (for $z<0$ and odd $M-N+1$ the right side is negative). $\sigma_N(M')$ is the infimum of $\|M'r\|_2$ over unit vectors $r\in\mathbb R^N$, which is the $N$-th singular value since $N\le M$; $\|B\|_2$ is the square root of the supremum of $\|Br\|_2^2$ over unit $r$. The probability is the product Gaussian measure on the entries of $G$.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, p. 70, Theorem 10 and equation (D.2)

import Mathlib
import Definitions.Def_AMPUniversality_Polytope_Certificate

set_option autoImplicit false
open MeasureTheory
open scoped NNReal ENNReal

namespace AMPUniversality.Polytope

/-- Theorem 10, p. 70 (cited from Bürgisser–Cucker [8], Theorem 1.1): for `N ≤ (1 − a)M`,
a deterministic `B ∈ ℝ^{M×N}` with `‖B‖₂ ≤ 1/a`, and `G` with i.i.d. `N(0, 1/M)` entries,
`P{σ_N(B + νG) ≤ νz} ≤ (a₁z)^{M−N+1}` for all `0 < z < a₂`, with `a₁, a₂` depending only
on `a`. The law of `G` is the product Gaussian measure on `Fin M → Fin N → ℝ`. -/
theorem theorem_10 :
    ∀ a : ℝ, 0 < a →
      ∃ a1 a2 : ℝ, 0 < a1 ∧ 0 < a2 ∧
        ∀ (M N : ℕ) (B : Matrix (Fin M) (Fin N) ℝ) (ν z : ℝ),
          (N : ℝ) ≤ (1 - a) * (M : ℝ) →
          Real.sqrt (sigmaMaxSq B) ≤ 1 / a →
          0 < ν → 0 < z → z < a2 →
          (Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin N =>
              ProbabilityTheory.gaussianReal 0 ((M : ℝ≥0)⁻¹))))
            {g : Fin M → Fin N → ℝ |
              sigmaMin (B + ν • Matrix.of g) Finset.univ ≤ ((ν * z : ℝ) : WithTop ℝ)}
            ≤ ENNReal.ofReal ((a1 * z) ^ (M - N + 1)) := by sorry

end AMPUniversality.Polytope
