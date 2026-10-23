-- Prove2me | Theorems.Thm_DavisGallegoTopaloglu2014_theorem_12_faithful
-- name    : DavisGallegoTopaloglu2014.theorem_12_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:30:21.58424+00:00
-- url     : https://prove2.me/theorems/ff9ab46c-430a-42e9-a07c-0bf6487f025f
-- title:
--   Theorem 12 with zero weights and $\gamma_i = 0$ allowed (powers-of-$\delta$ candidates)
-- statement:
--   Consider the nested logit model with nests $M$ and products $N = \{1, \dots, n\}$, $n \ge 1$, in every nest, revenues $r_{ij} \ge 0$ ordered so that $r_{i1} \ge \dots \ge r_{in}$, preference weights $v_{ij} \ge 0$, no-purchase weights $v_0 \ge 0$, $v_{i0} \ge 0$, and dissimilarity parameters $\gamma_i \ge 0$ (with $v_{i0} > 0$ whenever $\gamma_i = 0$) such that $\bar\gamma = \max_i \gamma_i > 1$. Let $\delta > 1$, $v^L_i = v_{i0} + \min_j v_{ij}$ (assumed positive) and $v^U_i = v_{i0} + \sum_j v_{ij}$, and let
--   $$l^L_i = \min\{l \in \mathbb Z : \delta^l \ge v^L_i\}, \qquad l^U_i = \min\{l \in \mathbb Z : \delta^l \ge v^U_i\}.$$
--   For $l^L_i \le l \le l^U_i$ let $\hat S_{il}$ be assortments such that, whenever some $S$ has $\delta^{l-1} \le V_i(S) \le \delta^l$, also $\delta^{l-1} \le V_i(\hat S_{il}) \le \delta^l$ and $\delta \sum_{j \in \hat S_{il}} r_{ij} v_{ij} \ge \sum_{j \in S} r_{ij} v_{ij}$ for all such $S$. If $(\hat x, \hat y)$ is an optimal solution of the linear program (4) with candidates $\{\hat S_{il} : l^L_i \le l \le l^U_i\} \cup \{\emptyset\}$ in nest $i$, then
--   $$v_0\, \delta^{2\bar\gamma+1} \hat x \ge \sum_i \delta^{\bar\gamma+1} \hat y_i, \qquad \delta^{\bar\gamma+1} \hat y_i \ge V_i(S)^{\gamma_i}\big(R_i(S) - \delta^{2\bar\gamma+1} \hat x\big) \quad \forall S \subseteq N,\ i \in M.$$
--
--   This is Theorem 12 of Davis, Gallego and Topaloglu (2014) on the paper's model. The platform theorem NestedLogitVariants.PowersDelta.theorem_12 proves it assuming in addition $v_{ij} > 0$ and $\gamma_i > 0$.
--
--   **Formalization Note** $l^L_i$, $l^U_i$ are `⌈log_δ v⌉`, equal to the paper's minima for $v > 0$; the hypothesis $v^L_i > 0$ is what the paper's definition of $l^L_i$ needs. As in the existing theorem, levels where no assortment fits impose nothing on $\hat S_{il}$ (taking $\emptyset$ there gives the paper's collection). The condition $\gamma_i = 0 \Rightarrow v_{i0} > 0$ avoids $0^0 = 1$ for an empty fully captured nest, which the paper leaves unspecified.
-- source:
--   Davis, Gallego, Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, Operations Research 62(2), 2014, doi:10.1287/opre.2014.1256, p. 28, Theorem 12 (§6 pp. 25-28; proof Appendix A.6 pp. 53-54)

import Mathlib
import Definitions.Def_NestedLogitVariants_PowersDelta_Model
import Definitions.Def_NestedLogitVariants_PowersDelta_Levels

open NestedLogitVariants.PowersDelta

theorem DavisGallegoTopaloglu2014.theorem_12_faithful {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n]
    (I : NestedLogitVariants.PowersDelta.Instance ι n)
    (hv0 : 0 ≤ I.v0) (hvnp : ∀ i, 0 ≤ I.vnp i) (hv : ∀ i j, 0 ≤ I.v i j)
    (hr : ∀ i j, 0 ≤ I.r i j) (hγ0 : ∀ i, 0 ≤ I.γ i) (hγv : ∀ i, I.γ i = 0 → 0 < I.vnp i)
    (hanti : ∀ i, Antitone (I.r i)) (hvL : ∀ i, 0 < vL I i)
    (γbar : ℝ) (hγbar : IsGreatest (Set.range I.γ) γbar) (hγbar1 : 1 < γbar)
    (δ : ℝ) (hδ : 1 < δ)
    (Sh : ι → ℤ → Finset (Fin n)) (hSh : IsPowersFamily I δ Sh)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (powersCandidates I δ Sh) xh yh) :
    LP3Feasible I (δ ^ (2 * γbar + 1) * xh) (δ ^ (γbar + 1) • yh) := by sorry
