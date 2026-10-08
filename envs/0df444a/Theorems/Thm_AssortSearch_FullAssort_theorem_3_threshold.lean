-- Prove2me | Theorems.Thm_AssortSearch_FullAssort_theorem_3_threshold
-- name    : AssortSearch.FullAssort.theorem_3_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:20.978302+00:00
-- url     : https://prove2.me/theorems/4b994e9d-7552-4d1f-a74a-4fc9a479c4c2
-- title:
--   Theorem 3 (the clause on $\bar U(S)$), p. 11 — $\bar U(S)$ is the unique solution of (4)
-- statement:
--   Let $\mu > 0$, $v_1, \dots, v_n > 0$, let $S \subsetneq N$ be an assortment, and let the search cost be $b > 0$. Then the equation (4)
--
--   $$\int_{u}^\infty (\bar y - u)\, w(\bar y, S)\, d\bar y = b$$
--
--   has exactly one solution $u \in \mathbb R$, and that solution is the search threshold $\bar U(S)$ (defined as the least $u$ at which the left-hand side is at most $b$).
--
--   This is the clause of Theorem 3 that makes the overlapping-assortment demand $q_i^{so}(S) = q_i^m(S)(1 - H(\bar U(S), S))$ well defined: a consumer searches if and only if her best in-store utility is below $\bar U(S)$.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 11 (PDF 13), Theorem 3, (4)

import Mathlib
import Definitions.Def_AssortSearch_FullAssort_Model

namespace AssortSearch.FullAssort

/-- Theorem 3, the clause on `Ū(S)` (p. 11): for an assortment `S ⊊ N` and a search cost
`b > 0`, equation (4), `∫_u^∞ (ȳ − u) w(ȳ, S) dȳ = b`, has exactly one solution `u`, and
that solution is `Ū(S)`. -/
theorem theorem_3_threshold {n : ℕ} (μ : ℝ) (hμ : 0 < μ) (v : Fin n → ℝ)
    (hv : ∀ i, 0 < v i) (S : Finset (Fin n)) (hS : S ≠ Finset.univ) (b : ℝ) (hb : 0 < b) :
    searchGain μ v S (Ubar μ v S b) = b ∧
      ∀ u : ℝ, searchGain μ v S u = b → u = Ubar μ v S b := by sorry

end AssortSearch.FullAssort
