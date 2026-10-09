-- Prove2me | Theorems.Thm_ConstATSP_Gap_vertebrate_tour_bound
-- name    : ConstATSP.Gap.vertebrate_tour_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:48:19.745559+00:00
-- url     : https://prove2.me/theorems/7ea68cb8-3674-4510-bc0d-6424a7a404db
-- title:
--   §11, Integrality gap, p. 61 — η′ = 21: a vertebrate pair has a tour of weight ≤ 2 value(I) + 21 lb(B̄) + w(B)
-- statement:
--   Let $(I,B)$ be a vertebrate pair, where $I=(G,\mathcal L,x,y)$ is a laminarly-weighted ATSP instance on at least two vertices. Then $G$ has a tour $F$ with
--   $$w_I(F)\le 2\,\mathrm{value}(I)+21\,\mathrm{lb}_I(\bar B)+w_I(B).$$
--
--   This is the non-constructive form of Corollary 10.2, used in §11 of the paper with $\kappa=2$ and $\eta'=21=1+5\cdot4$: Theorem 10.1 gives a $(4,\,2\,\mathrm{value}(I)+\mathrm{lb}_I(\bar B))$-light algorithm and Theorem 5.1 turns it into a tour of weight at most $5\cdot4\,\mathrm{lb}_I(\bar B)+2\,\mathrm{value}(I)+\mathrm{lb}_I(\bar B)+w_I(B)$. These constants feed Theorem 9.4.
--
--   **Formalization Note** The polynomial-time bound $2\,\mathrm{value}(I)+(37+36\varepsilon)\,\mathrm{lb}_I(\bar B)+w(B)$ of Corollary 10.2 is not formalized; this is its existential counterpart with the constant of §11. The instance is required to have at least two vertices.
-- source:
--   Svensson, Tarnawski, Végh, A constant-factor approximation algorithm for the asymmetric traveling salesman problem, J. ACM 67(6) (2020), accepted manuscript (LSE Research Online 106582), p. 61, §11, Integrality gap (η′ = 1 + 5 · 4); cf. p. 49, Corollary 10.2

import Mathlib
import Definitions.Def_ConstATSP_Gap_Graph
import Definitions.Def_ConstATSP_Gap_Instance

namespace ConstATSP.Gap

theorem vertebrate_tour_bound {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    (I : Instance V E) (hI : I.IsValid)
    (B : E → ℕ) (hB : I.IsVertebrate B) :
    ∃ F : E → ℕ, IsTour I.G F ∧ I.wt F ≤ 2 * I.value + 21 * I.lbCompl B + I.wt B := by sorry

end ConstATSP.Gap
