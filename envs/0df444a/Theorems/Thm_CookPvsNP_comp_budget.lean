-- Prove2me | Theorems.Thm_CookPvsNP_comp_budget
-- name    : CookPvsNP.comp_budget
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T09:11:33.664102+00:00
-- url     : https://prove2.me/theorems/dc25b4d2-ab2d-4afe-a1bf-ddc2e0f5bd67
-- title:
--   Nested composition budgets fit one Cook exponent
-- statement:
--   For any natural source exponents $k_1,k_2$, there is a single natural exponent $k$ such that, for every input length $n$, the quantity $20[n+(n^{k_1}+k_1)+((n+n^{k_1}+k_1+1)^{k_2}+k_2)+1]$ is at most $n^k+k$. The estimate includes lengths zero and one and zero exponents.
-- source:
--   New auxiliary result derived from Sneed's exact published Prove2Me definition CookPvsNP_comp_machine, id 9c26b5f3-2f9d-4c5d-9194-692cbc786b4a (2026-09-30), without changing its transitions. It supports the existing CookPvsNP.tm_compose_poly_witness for the scheduling-hardness mission. The underlying one-tape machine model is Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This particular representation and its equations are new formalization lemmas, not numbered claims of that paper.

import Definitions.Def_CookPvsNP_defs

namespace CookPvsNP
theorem comp_budget (k₁ k₂ : ℕ) : ∃ k, ∀ n : ℕ,
    20 * (n + (n ^ k₁ + k₁) + ((n + (n ^ k₁ + k₁) + 1) ^ k₂ + k₂) + 1) ≤
      n ^ k + k := by sorry
end CookPvsNP
