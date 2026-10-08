-- Prove2me | Theorems.Thm_AssortSearch_FullAssort_Ubar_limits
-- name    : AssortSearch.FullAssort.Ubar_limits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:21.715721+00:00
-- url     : https://prove2.me/theorems/4ffa8606-110f-4c68-a271-29984945b060
-- title:
--   Proof of Theorem 6, p. 18 — $\bar U(S)\to-\infty$ as $b\to\infty$ and $\bar U(S)\to\infty$ as $b\to0$
-- statement:
--   Let $\mu > 0$, $v_1, \dots, v_n > 0$, and $S \subsetneq N$. Then the search threshold $\bar U_b(S)$ satisfies
--
--   $$\lim_{b \to \infty} \bar U_b(S) = -\infty \qquad\text{and}\qquad \lim_{b \to 0^+} \bar U_b(S) = +\infty .$$
--
--   The paper asserts both limits in the proof of Theorem 6. The second one is what drives the theorem: as search becomes free, a consumer searches unless her in-store utility is arbitrarily high.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 18 (PDF 20), proof of Theorem 6

import Mathlib
import Definitions.Def_AssortSearch_FullAssort_Model

namespace AssortSearch.FullAssort

open Filter Topology

/-- Proof of Theorem 6 (p. 18): for an assortment `S ⊊ N`,
`lim_{b→∞} Ū(S) = −∞` and `lim_{b→0⁺} Ū(S) = ∞`. -/
theorem Ubar_limits {n : ℕ} (μ : ℝ) (hμ : 0 < μ) (v : Fin n → ℝ)
    (hv : ∀ i, 0 < v i) (S : Finset (Fin n)) (hS : S ≠ Finset.univ) :
    Tendsto (fun b => Ubar μ v S b) atTop atBot ∧
      Tendsto (fun b => Ubar μ v S b) (𝓝[>] 0) atTop := by sorry

end AssortSearch.FullAssort
