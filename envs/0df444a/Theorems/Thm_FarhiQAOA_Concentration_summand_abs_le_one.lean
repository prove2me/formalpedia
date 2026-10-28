-- Prove2me | Theorems.Thm_FarhiQAOA_Concentration_summand_abs_le_one
-- name    : FarhiQAOA.Concentration.summand_abs_le_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:08.811653+00:00
-- url     : https://prove2.me/theorems/5f1fa6d7-fe4a-4465-9c61-f398f35ae08d
-- title:
--   Section III, p. 7, after (30) — each summand of (28) is at most 1 in absolute value
-- statement:
--   Let $G$ be a graph on $n$ vertices, $p\ge0$, $\boldsymbol\gamma,\boldsymbol\beta\in\mathbb R^p$, and let $j,k,j',k'$ be qubits. Then the summand of (28) satisfies
--   $$\Big|\langle\boldsymbol\gamma,\boldsymbol\beta|C_{\langle jk\rangle}C_{\langle j'k'\rangle}|\boldsymbol\gamma,\boldsymbol\beta\rangle-\langle\boldsymbol\gamma,\boldsymbol\beta|C_{\langle jk\rangle}|\boldsymbol\gamma,\boldsymbol\beta\rangle\,\langle\boldsymbol\gamma,\boldsymbol\beta|C_{\langle j'k'\rangle}|\boldsymbol\gamma,\boldsymbol\beta\rangle\Big|\le 1 .$$
--
--   Together with the count (29), this bounds the variance (27) by (29) times $m$.
--
--   **Formalization Note** The statement concerns the QAOA state itself, whose measurement probabilities sum to one because the QAOA operator is unitary; that normalisation is part of what is to be shown, not a hypothesis. Expectations are sums $\sum_z|\langle z|\boldsymbol\gamma,\boldsymbol\beta\rangle|^2(\cdot)(z)$.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm, arXiv:1411.4028v1, p. 7, Section III, after (30)

import Mathlib
import Definitions.Def_FarhiQAOA_Concentration_Setting

namespace FarhiQAOA.Concentration

theorem summand_abs_le_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : ℕ)
    (γ β : Fin p → ℝ) (j k j' k' : Fin n) :
    |edgeCov G p γ β j k j' k'| ≤ 1 := by sorry

end FarhiQAOA.Concentration
