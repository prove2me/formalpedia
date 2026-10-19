-- Prove2me | Theorems.Thm_CoopCluster_EvenSplit_proposition_3_i
-- name    : CoopCluster.EvenSplit.proposition_3_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:14.493386+00:00
-- url     : https://prove2.me/theorems/812b6c87-1224-44fd-9c73-6dc76f6a3cda
-- title:
--   Proposition 3(i), at t = 0, p. 113 (PDF 8) — a symmetric equilibrium exists, and αO and PO = D(αO)/(2β0 + θ) satisfy the first-order equation
-- statement:
--   Consider the co-opetition game of §4 with an even cost split ($t=0$), under the standing assumptions and price-competition intensity $\theta\ge 0$. Write $D(\alpha)=B-\beta_0\gamma-hw e^{-\delta\alpha}$.
--
--   1. A symmetric equilibrium $(P^O,\alpha^O)$ exists.
--   2. Every symmetric equilibrium $(P^O,\alpha^O)$ satisfies
--   $$2D(\alpha^O)\,hw\delta-(2\beta_0+\theta)\,c\,\alpha^O e^{\delta\alpha^O}=0,
--   \qquad P^O=\frac{D(\alpha^O)}{2\beta_0+\theta},$$
--   so the equilibrium price is $p^O=P^O+\gamma$.
--
--   This is the characterization of the co-opetition equilibrium that the comparison with monopoly (Proposition 7) is built on.
--
--   **Formalization Note.** The page states Proposition 3 for every $t\ge 0$; at $t=0$ the terms $t(\beta_0+2\theta)C(\alpha)$ vanish and the displayed equations reduce to the ones above. Only $t=0$ is formalized, the case Proposition 7 uses. Existence is stated because the paper speaks of "the" equilibrium; uniqueness of the root of the first-order equation is not claimed on the page and is not asserted. Margins and deviations range over $P\ge 0$.
-- source:
--   Yuan, Dai, Chen & Gavirneni, Co-opetition in service clusters with waiting-area entertainment, MSOM 23(1):106–122 (2021), p. 113 (PDF 8), Proposition 3(i), specialised to t = 0

import Mathlib
import Definitions.Def_CoopCluster_EvenSplit_Model

namespace CoopCluster.EvenSplit

theorem proposition_3_i (M : Params) (hS : M.Standing) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∃ P α : ℝ, IsSymEq M θ 0 P α) ∧
      ∀ P α : ℝ, IsSymEq M θ 0 P α →
        2 * D M α * M.h * M.w * M.δ - (2 * M.b0 + θ) * M.c * α * Real.exp (M.δ * α) = 0 ∧
        P = D M α / (2 * M.b0 + θ) := by sorry

end CoopCluster.EvenSplit
