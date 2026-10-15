-- Prove2me | Theorems.Thm_FarhiQAOA_Concentration_eq_30
-- name    : FarhiQAOA.Concentration.eq_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:09.679742+00:00
-- url     : https://prove2.me/theorems/18e44c2f-5118-4eb1-9285-bc5d4c9eb3d5
-- title:
--   Section III, (30), p. 7 — on v-regular graphs, ⟨C²⟩ − ⟨C⟩² ≤ 2[((v−1)^{2p+2}−1)/((v−1)−1)]·m in every QAOA state
-- statement:
--   Let $G$ be a $v$-regular graph on $n$ vertices with $m$ edges, where $v\ge3$, let $p\ge1$, and let $\boldsymbol\gamma=(\gamma_1,\dots,\gamma_p)$, $\boldsymbol\beta=(\beta_1,\dots,\beta_p)$ be arbitrary real angles. Let $C$ be the MaxCut objective of $G$ (the number of cut edges, eq. (11)) and
--   $$|\boldsymbol\gamma,\boldsymbol\beta\rangle=U(B,\beta_p)U(C,\gamma_p)\cdots U(B,\beta_1)U(C,\gamma_1)|s\rangle$$
--   the QAOA state (6). Then the variance of $C$ measured in this state satisfies
--   $$\langle\boldsymbol\gamma,\boldsymbol\beta|C^2|\boldsymbol\gamma,\boldsymbol\beta\rangle-\langle\boldsymbol\gamma,\boldsymbol\beta|C|\boldsymbol\gamma,\boldsymbol\beta\rangle^2\le 2\left[\frac{(v-1)^{2p+2}-1}{(v-1)-1}\right]\cdot m .$$
--
--   For fixed $v$ and $p$ the standard deviation of the cut value is therefore $O(\sqrt m)$: the distribution of $C(z)$ obtained by measuring $|\boldsymbol\gamma,\boldsymbol\beta\rangle$ is concentrated around its mean $F_p(\boldsymbol\gamma,\boldsymbol\beta)$.
--
--   **Formalization Note** The variance is $\sum_z P(z)C(z)^2-\big(\sum_z P(z)C(z)\big)^2$ with $P(z)=|\langle z|\boldsymbol\gamma,\boldsymbol\beta\rangle|^2$, which equals the operator expression since $C$ is diagonal. The angles range over all of $\mathbb R^p$; the paper restricts them to $[0,2\pi]$ and $[0,\pi]$ by periodicity only, and the bound does not use the range. The hypothesis $v\ge3$ is the domain of the printed formula (its denominator vanishes at $v=2$, which the paper treats separately as $4p+4$). The edge count $m$ counts each edge once.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm, arXiv:1411.4028v1, p. 7, Section III, (30)

import Mathlib
import Definitions.Def_FarhiQAOA_Concentration_Setting

namespace FarhiQAOA.Concentration

theorem eq_30 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : ℕ)
    (γ β : Fin p → ℝ) (v : ℕ) (hv : 3 ≤ v) (hreg : G.IsRegularOfDegree v) (hp : 1 ≤ p) :
    cutVariance G p γ β ≤
      2 * ((((v : ℝ) - 1) ^ (2 * p + 2) - 1) / (((v : ℝ) - 1) - 1)) * (edgePairs G).card := by sorry

end FarhiQAOA.Concentration
