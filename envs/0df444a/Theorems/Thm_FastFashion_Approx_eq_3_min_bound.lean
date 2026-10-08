-- Prove2me | Theorems.Thm_FastFashion_Approx_eq_3_min_bound
-- name    : FastFashion.Approx.eq_3_min_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:14:25.243981+00:00
-- url     : https://prove2.me/theorems/d4adb7b6-3140-484d-a231-4ac9c24c0515
-- title:
--   Eq. (3) — the expected truncated first stockout time of a set of sizes is at most the minimum over its sizes
-- statement:
--   In the setting of the model file (independent Poisson family with rates $\lambda_s > 0$, period $T > 0$), for every nonempty set of sizes $\mathcal D \subseteq \mathcal S$ and every $q \in \mathbb N^{\mathcal S}$,
--   $$\mathbb E[\tau_{\mathcal D} \wedge T] \le \min_{s \in \mathcal D} \mathbb E[\tau_s \wedge T].$$
--
--   This is the first of the two approximation steps of §3.1.3, each of which produces an upper bound.
--
--   **Formalization Note** The paper writes "for any subset of sizes $\mathcal D \subset \mathcal S$"; the subset is required to be nonempty here, since the minimum over the empty set has no value. $\mathbb E[\tau_s \wedge T]$ is $h^{\{s\}}(q)$.
-- source:
--   Caro & Gallien, Inventory Management of a Fast-Fashion Retail Network, working paper (August 2, 2007), p. 12, Eq. (3)

import Mathlib
import Definitions.Def_FastFashion_Structure_Model

namespace FastFashion.Approx

open MeasureTheory ProbabilityTheory

/-- Eq. (3) (Caro–Gallien, p. 12): for every nonempty set of sizes `D`,
`𝔼[τ_D ∧ T] ≤ min_{s ∈ D} 𝔼[τ_s ∧ T]`. -/
theorem eq_3_min_bound {S Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (lam : S → ℝ) (N : S → ℝ → Ω → ℕ)
    (hN : FastFashion.Structure.IsPoissonFamily lam N P) (hlam : ∀ s, 0 < lam s) (T : ℝ) (hT : 0 < T)
    (D : Finset S) (hD : D.Nonempty) (q : S → ℕ) :
    FastFashion.Structure.hA N P T D q ≤ D.inf' hD (fun s => FastFashion.Structure.hA N P T {s} q) := by sorry

end FastFashion.Approx
