-- Prove2me | Theorems.Thm_FastFashion_Approx_eq_2_optional_sampling
-- name    : FastFashion.Approx.eq_2_optional_sampling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:14:26.12029+00:00
-- url     : https://prove2.me/theorems/f0339317-7992-48c2-a99e-72a39af030cb
-- title:
--   Eq. (2) — expected sales as a rate-weighted sum of expected truncated stockout times
-- statement:
--   Let $(N_s)_{s\in\mathcal S}$ be an independent Poisson family with rates $\lambda_s > 0$, let $T > 0$, and let $\mathcal S^+ \subseteq \mathcal S$ be the major sizes with $\mathcal S^- = \mathcal S \setminus \mathcal S^+$. Then for every inventory vector $q \in \mathbb N^{\mathcal S}$ the expected sales $g_\lambda(q) = \mathbb E[G(q)]$ of (1) satisfy
--   $$g_\lambda(q) = \lambda_{\mathcal S^+}\,\mathbb E[\tau_{\mathcal S^+} \wedge T] + \sum_{s \in \mathcal S^-} \lambda_s\, \mathbb E[\tau_{\mathcal S^+ \cup \{s\}} \wedge T], \qquad \lambda_{\mathcal S^+} = \sum_{s \in \mathcal S^+}\lambda_s .$$
--
--   The identity turns the expected sales into a combination of expected truncated stopping times, which is the starting point of the approximation of §3.1.3.
--
--   **Formalization Note** $\mathbb E[\tau_{\mathcal A} \wedge T]$ is $h^{\mathcal A}(q)$ of the model file. The statement holds also for $\mathcal S^+ = \emptyset$ (then $\tau_{\emptyset} \wedge T = T$ and the first term vanishes), so no nonemptiness is assumed.
-- source:
--   Caro & Gallien, Inventory Management of a Fast-Fashion Retail Network, working paper (August 2, 2007), p. 12, Eq. (2)

import Mathlib
import Definitions.Def_FastFashion_Structure_Model

namespace FastFashion.Approx

open MeasureTheory ProbabilityTheory

/-- Eq. (2) (Caro–Gallien, p. 12): under independent Poisson demand,
`g_λ(q) = λ_{S⁺} 𝔼[τ_{S⁺} ∧ T] + ∑_{s ∈ S⁻} λ_s 𝔼[τ_{S⁺ ∪ {s}} ∧ T]`, with `λ_{S⁺} = ∑_{s ∈ S⁺} λ_s`. -/
theorem eq_2_optional_sampling {S Ω : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (lam : S → ℝ) (N : S → ℝ → Ω → ℕ)
    (hN : FastFashion.Structure.IsPoissonFamily lam N P) (hlam : ∀ s, 0 < lam s) (T : ℝ) (hT : 0 < T)
    (Sp : Finset S) (q : S → ℕ) :
    FastFashion.Structure.expectedSales N P Sp T q =
      (∑ s ∈ Sp, lam s) * FastFashion.Structure.hA N P T Sp q + ∑ s ∈ Spᶜ, lam s * FastFashion.Structure.hA N P T (insert s Sp) q := by sorry

end FastFashion.Approx
