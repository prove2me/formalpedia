-- Prove2me | Theorems.Thm_FastFashion_Approx_eq_4_5_single_size
-- name    : FastFashion.Approx.eq_4_5_single_size
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:15:10.283984+00:00
-- url     : https://prove2.me/theorems/120790de-97d3-404c-a40c-2b30ed6ad32f
-- title:
--   Eqs. (4)–(5) — $\mathbb E[\tau_s \wedge T]$ as a sum of Poisson tail probabilities and of incomplete Gamma ratios
-- statement:
--   In the setting of the model file (independent Poisson family with rates $\lambda_s > 0$, period $T > 0$), for every size $s$ and every $q \in \mathbb N^{\mathcal S}$,
--   $$\mathbb E[\tau_s \wedge T] = \frac{1}{\lambda_s}\sum_{k=1}^{q_s} \mathbb P\big(N_s(T) \ge k\big) = \sum_{k=1}^{q_s} \frac{\gamma(k, \lambda_s T)}{\lambda_s\,\Gamma(k)},$$
--   where $\Gamma(k) = (k-1)!$ and $\gamma(a,b) = \int_0^b v^{a-1}e^{-v}\,dv$ is the lower incomplete Gamma function.
--
--   The formula makes the minimum operand of (3) explicitly computable and exhibits it as a sum of $q_s$ terms.
--
--   **Formalization Note** Both equalities are stated as a conjunction. $\mathbb P(E)$ is the real number `(P E).toReal`. Each index $k$ ranges over $1, \dots, q_s$, so $\gamma(k, \cdot)$ and $(k-1)!$ are evaluated only at $k \ge 1$. The empty sum ($q_s = 0$) gives $\mathbb E[\tau_s(0) \wedge T] = 0$.
-- source:
--   Caro & Gallien, Inventory Management of a Fast-Fashion Retail Network, working paper (August 2, 2007), p. 12, Eqs. (4)–(5)

import Mathlib
import Definitions.Def_FastFashion_Structure_Model
import Definitions.Def_FastFashion_Approx_Tangents

namespace FastFashion.Approx

open MeasureTheory ProbabilityTheory

/-- Eqs. (4)–(5) (Caro–Gallien, p. 12): for every size `s`,
`𝔼[τ_s ∧ T] = (1/λ_s) ∑_{k=1}^{q_s} ℙ(N_s(T) ≥ k) = ∑_{k=1}^{q_s} γ(k, λ_s T) / (λ_s Γ(k))`,
with `Γ(k) = (k − 1)!`. -/
theorem eq_4_5_single_size {S Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (lam : S → ℝ) (N : S → ℝ → Ω → ℕ)
    (hN : FastFashion.Structure.IsPoissonFamily lam N P) (hlam : ∀ s, 0 < lam s) (T : ℝ) (hT : 0 < T)
    (s : S) (q : S → ℕ) :
    FastFashion.Structure.hA N P T {s} q =
        (1 / lam s) * ∑ k ∈ Finset.Icc 1 (q s), (P {ω | k ≤ N s T ω}).toReal ∧
      FastFashion.Structure.hA N P T {s} q =
        ∑ k ∈ Finset.Icc 1 (q s),
          lowerGamma k (lam s * T) / (lam s * (Nat.factorial (k - 1) : ℝ)) := by sorry

end FastFashion.Approx
