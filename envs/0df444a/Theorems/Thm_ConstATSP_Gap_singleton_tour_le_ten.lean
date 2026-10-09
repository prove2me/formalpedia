-- Prove2me | Theorems.Thm_ConstATSP_Gap_singleton_tour_le_ten
-- name    : ConstATSP.Gap.singleton_tour_le_ten
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:47:18.591774+00:00
-- url     : https://prove2.me/theorems/81f982d6-aa8d-4dd4-afc3-561e74947a3b
-- title:
--   §11, Integrality gap, p. 61 — α′_S = 10: every singleton instance has a tour of weight ≤ 10 value(I)
-- statement:
--   Let $I=(G,\mathcal L,x,y)$ be a laminarly-weighted ATSP instance on at least two vertices that is a singleton instance (every set of $\mathcal L$ is a singleton). Then $G$ has a tour $F$ with
--   $$w_I(F)\le 10\,\mathrm{value}(I).$$
--
--   This is the non-constructive form of Corollary 5.2, used in §11 of the paper ("non-constructively we can have $\alpha'_S=10$"): Theorem 4.1 gives a $(2,0)$-light algorithm for $B=\emptyset$, Theorem 5.1 then gives a tour of weight at most $5\cdot2\cdot\mathrm{lb}(V)$, and $\mathrm{lb}(V)=\mathrm{value}(I)$ for singleton instances. The constant $\alpha'_S=10$ enters the final bound $319$.
--
--   **Formalization Note** The polynomial-time $(18+\varepsilon)$-approximation of Corollary 5.2 is not formalized; this is its existential counterpart with the constant of §11. The instance is required to have at least two vertices.
-- source:
--   Svensson, Tarnawski, Végh, A constant-factor approximation algorithm for the asymmetric traveling salesman problem, J. ACM 67(6) (2020), accepted manuscript (LSE Research Online 106582), p. 61, §11, Integrality gap (α′_S = 10); cf. p. 17, Corollary 5.2

import Mathlib
import Definitions.Def_ConstATSP_Gap_Graph
import Definitions.Def_ConstATSP_Gap_Instance

namespace ConstATSP.Gap

theorem singleton_tour_le_ten {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    (I : Instance V E) (hI : I.IsValid)
    (hS : I.IsSingleton) :
    ∃ F : E → ℕ, IsTour I.G F ∧ I.wt F ≤ 10 * I.value := by sorry

end ConstATSP.Gap
