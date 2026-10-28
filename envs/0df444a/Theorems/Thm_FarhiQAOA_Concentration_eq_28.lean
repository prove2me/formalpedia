-- Prove2me | Theorems.Thm_FarhiQAOA_Concentration_eq_28
-- name    : FarhiQAOA.Concentration.eq_28
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:03.466821+00:00
-- url     : https://prove2.me/theorems/19e34fa3-f98b-411c-9dea-2fd0443db424
-- title:
--   Section III, (27)–(28), p. 7 — the variance of C in |γ,β⟩ is the double sum of edge covariances
-- statement:
--   Let $G$ be a graph on $n$ vertices with edge set $\{\langle jk\rangle\}$, let $p\ge 0$ and $\boldsymbol\gamma,\boldsymbol\beta\in\mathbb R^p$, and let $|\boldsymbol\gamma,\boldsymbol\beta\rangle$ be the QAOA state for the MaxCut objective $C=\sum_{\langle jk\rangle} C_{\langle jk\rangle}$. Then the variance of $C$ in this state splits over pairs of edges:
--   $$\langle\boldsymbol\gamma,\boldsymbol\beta|C^2|\boldsymbol\gamma,\boldsymbol\beta\rangle-\langle\boldsymbol\gamma,\boldsymbol\beta|C|\boldsymbol\gamma,\boldsymbol\beta\rangle^2=\sum_{\langle jk\rangle}\sum_{\langle j'k'\rangle}\Big[\langle C_{\langle jk\rangle}C_{\langle j'k'\rangle}\rangle-\langle C_{\langle jk\rangle}\rangle\,\langle C_{\langle j'k'\rangle}\rangle\Big],$$
--   where $\langle X\rangle=\langle\boldsymbol\gamma,\boldsymbol\beta|X|\boldsymbol\gamma,\boldsymbol\beta\rangle$ and both sums run over all edges, each edge once (ordered pairs of edges, including $\langle j'k'\rangle=\langle jk\rangle$).
--
--   This is the decomposition (28) on which the concentration bound (30) rests: each summand is the covariance of two clause operators in the QAOA state.
--
--   **Formalization Note** All expectations are written as $\sum_z |\langle z|\boldsymbol\gamma,\boldsymbol\beta\rangle|^2\,(\cdot)(z)$, which equals the operator expectation since every operator involved is diagonal in the computational basis. The identity is stated for every $p\ge0$ and all real angles; it uses no normalisation of the state.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm, arXiv:1411.4028v1, p. 7, Section III, (27)–(28)

import Mathlib
import Definitions.Def_FarhiQAOA_Concentration_Setting

namespace FarhiQAOA.Concentration

theorem eq_28 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : ℕ)
    (γ β : Fin p → ℝ) :
    cutVariance G p γ β =
      ∑ e ∈ edgePairs G, ∑ e' ∈ edgePairs G, edgeCov G p γ β e.1 e.2 e'.1 e'.2 := by sorry

end FarhiQAOA.Concentration
