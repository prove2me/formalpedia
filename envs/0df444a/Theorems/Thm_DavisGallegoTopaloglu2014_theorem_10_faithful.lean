-- Prove2me | Theorems.Thm_DavisGallegoTopaloglu2014_theorem_10_faithful
-- name    : DavisGallegoTopaloglu2014.theorem_10_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:30:06.58+00:00
-- url     : https://prove2.me/theorems/06c54496-5ad1-4704-84dc-b3d442fd7490
-- title:
--   Theorem 10 with zero weights and $\gamma_i = 0$ allowed (factor two for partially captured nests)
-- statement:
--   Consider the nested logit model with nests $M$ and products $N = \{1, \dots, n\}$ in every nest, revenues $r_{ij} \ge 0$ ordered so that $r_{i1} \ge \dots \ge r_{in}$, preference weights $v_{ij} \ge 0$, no-purchase weights $v_0 \ge 0$ and $v_{i0} \ge 0$, and dissimilarity parameters $0 \le \gamma_i \le 1$, where $\gamma_i = 0$ is allowed only in a partially captured nest ($v_{i0} > 0$). For a capacity $\epsilon \ge 0$ let $\hat z_i(\epsilon)$ be the greedy solution of the continuous knapsack
--   $$\max \Big\{ \sum_j r_{ij} v_{ij} z_j : \sum_j v_{ij} z_j \le \epsilon,\ 0 \le z_j \le \mathbb 1(v_{ij} \le \epsilon) \Big\}$$
--   that fills eligible products in revenue order, and $\hat S_i(\epsilon) = \{j : \hat z_{ij}(\epsilon) = 1\}$. Let $(\hat x, \hat y)$ be an optimal solution of the linear program (4) with candidate assortments $\{\hat S_i(\epsilon) : \epsilon \ge 0\} \cup \{\{j\} : j \in N\}$ in nest $i$. Then
--   $$v_0\, 2\hat x \ge \sum_{i \in M} 2\hat y_i, \qquad 2\hat y_i \ge V_i(S)^{\gamma_i}\big(R_i(S) - 2\hat x\big) \quad \forall S \subseteq N,\ i \in M.$$
--
--   This is Theorem 10 of Davis, Gallego and Topaloglu (2014) on the paper's full model. The platform theorem NestedLogitVariants.PartialCompetitive.theorem_10 proves it assuming in addition $v_{ij} > 0$ and $\gamma_i > 0$.
--
--   **Formalization Note** With the existing definition `zhat`, a zero-weight product gets $\hat z_{ij} = 0$ (division by zero), whereas the paper's greedy would take it fully; since such a product changes neither $V_i$ nor $R_i$, the constraints of (4) are the same. The condition $\gamma_i = 0 \Rightarrow v_{i0} > 0$ avoids $0^0 = 1$ for an empty fully captured nest, a case the paper leaves unspecified. $\epsilon = \infty$ is covered by large real capacities.
-- source:
--   Davis, Gallego, Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, Operations Research 62(2), 2014, doi:10.1287/opre.2014.1256, p. 24, Theorem 10 (§5 pp. 22-24; proof Appendix A.3 pp. 45-46)

import Mathlib
import Definitions.Def_NestedLogitVariants_PartialCompetitive_Model
import Definitions.Def_NestedLogitVariants_PartialCompetitive_Knapsack

open NestedLogitVariants.PartialCompetitive

theorem DavisGallegoTopaloglu2014.theorem_10_faithful {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.PartialCompetitive.Instance ι n)
    (hv0 : 0 ≤ I.v0) (hvnp : ∀ i, 0 ≤ I.vnp i) (hv : ∀ i j, 0 ≤ I.v i j)
    (hr : ∀ i j, 0 ≤ I.r i j) (hγ0 : ∀ i, 0 ≤ I.γ i) (hγv : ∀ i, I.γ i = 0 → 0 < I.vnp i)
    (hanti : ∀ i, Antitone (I.r i))
    (hγ : ∀ i, I.γ i ≤ 1)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (candidates I) xh yh) :
    LP3Feasible I (2 * xh) (2 • yh) := by sorry
