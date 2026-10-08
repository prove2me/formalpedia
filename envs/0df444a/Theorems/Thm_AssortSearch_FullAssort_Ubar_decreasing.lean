-- Prove2me | Theorems.Thm_AssortSearch_FullAssort_Ubar_decreasing
-- name    : AssortSearch.FullAssort.Ubar_decreasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:10.407188+00:00
-- url     : https://prove2.me/theorems/4e2599e3-5e70-485e-9abd-ce1d2774c2fa
-- title:
--   Proof of Theorem 6, p. 18 — $\bar U(S)$ is decreasing in the search cost $b$
-- statement:
--   Let $\mu > 0$, $v_1, \dots, v_n > 0$, and $S \subsetneq N$. Then the search threshold $\bar U_b(S)$, viewed as a function of the search cost $b > 0$, is strictly decreasing:
--
--   $$0 < b < b' \implies \bar U_{b'}(S) < \bar U_b(S).$$
--
--   The paper asserts this ("from the search rule specified in Theorem 3") in the proof of Theorem 6: cheaper search makes consumers more demanding.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 18 (PDF 20), proof of Theorem 6

import Mathlib
import Definitions.Def_AssortSearch_FullAssort_Model

namespace AssortSearch.FullAssort

/-- Proof of Theorem 6 (p. 18): for an assortment `S ⊊ N`, the search threshold `Ū(S)` is
(strictly) decreasing in the search cost `b > 0`. -/
theorem Ubar_decreasing {n : ℕ} (μ : ℝ) (hμ : 0 < μ) (v : Fin n → ℝ)
    (hv : ∀ i, 0 < v i) (S : Finset (Fin n)) (hS : S ≠ Finset.univ) :
    StrictAntiOn (fun b => Ubar μ v S b) (Set.Ioi 0) := by sorry

end AssortSearch.FullAssort
