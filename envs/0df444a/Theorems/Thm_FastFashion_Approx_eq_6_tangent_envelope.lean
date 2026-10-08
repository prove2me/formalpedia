-- Prove2me | Theorems.Thm_FastFashion_Approx_eq_6_tangent_envelope
-- name    : FastFashion.Approx.eq_6_tangent_envelope
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:14:59.994984+00:00
-- url     : https://prove2.me/theorems/7d729766-443c-4a7e-b575-307562646539
-- title:
--   Eq. (6) — $\mathbb E[\tau_s \wedge T]$ is the lower envelope of its discrete tangents (coefficients index-corrected)
-- statement:
--   In the setting of the model file (independent Poisson family with rates $\lambda_s > 0$, period $T > 0$), for every size $s$ and every $q \in \mathbb N^{\mathcal S}$,
--   $$\mathbb E[\tau_s \wedge T] = \min_{i \in \mathbb N \cup \{\infty\}} \big\{a_i(\lambda_s)(q_s - i) + b_i(\lambda_s)\big\},$$
--   where $a_i(\lambda) = \gamma(i+1,\lambda T)/(\lambda\, i!)$, $b_i(\lambda) = \sum_{k=0}^{i-1} a_k(\lambda)$, and the tangent with index $\infty$ is the constant $T$. That is, every discrete tangent lies above $\mathbb E[\tau_s \wedge T]$ at $q_s$, and some tangent equals it.
--
--   This representation is what the approximation (8) truncates to finitely many tangents.
--
--   **Formalization Note** *Corrected coefficients.* The paper prints $a_k = \gamma(k,\lambda_s T)/(\lambda_s\Gamma(k))$ and $b_i = \sum_{k=0}^{i-1} a_k$, under which $b_1 = a_0$ involves $\Gamma(0)$ and (6) fails; the slopes here are re-indexed so that $a_k$ is the $(k+1)$-th term of (5), matching the paper's own description of $a_k$. *Minimum.* The paper takes the minimum over $i \in \mathbb N$ and extends $a, b$ to $i = \infty$; the statement takes it over $\mathbb N \cup \{\infty\}$, and the infinite tangent does not change the minimum. The minimum is stated as `IsLeast` of the set of tangent values (lower bound and attainment), not as a real infimum.
-- source:
--   Caro & Gallien, Inventory Management of a Fast-Fashion Retail Network, working paper (August 2, 2007), p. 12, Eq. (6) (a_k index corrected)

import Mathlib
import Definitions.Def_FastFashion_Structure_Model
import Definitions.Def_FastFashion_Approx_Tangents

namespace FastFashion.Approx

open MeasureTheory ProbabilityTheory

/-- Eq. (6) (Caro–Gallien, p. 12), with the slopes re-indexed so that `a_k` is the `(k+1)`-th term
of (5): `𝔼[τ_s ∧ T]` is the least value of the discrete tangents
`a_i(λ_s)(q_s − i) + b_i(λ_s)`, `i ∈ ℕ ∪ {∞}` (the tangent at `∞` being the constant `T`), and the
least value is attained. -/
theorem eq_6_tangent_envelope {S Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (lam : S → ℝ) (N : S → ℝ → Ω → ℕ)
    (hN : FastFashion.Structure.IsPoissonFamily lam N P) (hlam : ∀ s, 0 < lam s) (T : ℝ) (hT : 0 < T)
    (s : S) (q : S → ℕ) :
    IsLeast (Set.range fun i : WithTop ℕ => tangent (lam s) T i (q s : ℝ)) (FastFashion.Structure.hA N P T {s} q) := by sorry

end FastFashion.Approx
