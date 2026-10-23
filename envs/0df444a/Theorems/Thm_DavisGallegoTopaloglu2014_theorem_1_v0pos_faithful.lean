-- Prove2me | Theorems.Thm_DavisGallegoTopaloglu2014_theorem_1_v0pos_faithful
-- name    : DavisGallegoTopaloglu2014.theorem_1_v0pos_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:29:59.443592+00:00
-- url     : https://prove2.me/theorems/fac8dabd-25b6-4751-96f2-8843ec6e8c4a
-- title:
--   Theorem 1 with $v_0 > 0$ on the paper's full model (LP-based approximation framework)
-- statement:
--   Consider the nested logit model with nests $M$ and products $N = \{1, \dots, n\}$ in every nest, revenues $r_{ij} \ge 0$ ordered so that $r_{i1} \ge \dots \ge r_{in}$, preference weights $v_{ij} \ge 0$, within-nest no-purchase weights $v_{i0} \ge 0$, dissimilarity parameters $\gamma_i \ge 0$ (with $v_{i0} > 0$ whenever $\gamma_i = 0$), and a no-purchase weight $v_0 > 0$. Let $V_i(S) = v_{i0} + \sum_{j \in S} v_{ij}$, $R_i(S) = \sum_{j \in S} r_{ij} v_{ij} / V_i(S)$, and
--   $$\Pi(S_1, \dots, S_m) = \frac{\sum_i V_i(S_i)^{\gamma_i} R_i(S_i)}{v_0 + \sum_i V_i(S_i)^{\gamma_i}}, \qquad Z^* = \max_S \Pi(S).$$
--   For candidate collections $A_i$, let $(\hat x, \hat y)$ be an optimal solution of the linear program (4), $\min x$ s.t. $v_0 x \ge \sum_i y_i$ and $y_i \ge V_i(S)^{\gamma_i}(R_i(S) - x)$ for $S \in A_i$, and let $\hat S_i \in A_i$ maximize $V_i(S)^{\gamma_i}(R_i(S) - \hat x)$ over $A_i$. If $(\alpha \hat x, \beta \hat y)$ satisfies the constraints of (4) for every $S \subseteq N$ (problem (3)) for some reals $\alpha, \beta$, then
--   $$\alpha\, \Pi(\hat S) \ge Z^* \ge \Pi(\hat S).$$
--
--   This is Theorem 1 of Davis, Gallego and Topaloglu (2014) with the hypothesis $v_0 > 0$, which the printed statement lacks and needs (it fails for $v_0 = 0$). The platform theorem NestedLogitVariants.LP.theorem_1 proves it assuming in addition $v_{ij} > 0$ and $\gamma_i > 0$.
--
--   **Formalization Note** $Z^*$ is $\Pi(S^*)$ for an arbitrary optimal $S^*$. Division is total ($x/0 = 0$), giving $R_i(\emptyset) = 0$. The condition $\gamma_i = 0 \Rightarrow v_{i0} > 0$ avoids the real power $0^0 = 1$ for an empty fully captured nest, which the paper leaves unspecified.
-- source:
--   Davis, Gallego, Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, Operations Research 62(2), 2014, doi:10.1287/opre.2014.1256, p. 13, Theorem 1 and display (5) (model p. 7; LPs (3), (4) pp. 11-12)

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model

open NestedLogitVariants.LP

theorem DavisGallegoTopaloglu2014.theorem_1_v0pos_faithful {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n)
    (hv0 : 0 < I.v0) (hvnp : ∀ i, 0 ≤ I.vnp i) (hv : ∀ i j, 0 ≤ I.v i j)
    (hr : ∀ i j, 0 ≤ I.r i j) (hγ0 : ∀ i, 0 ≤ I.γ i) (hγv : ∀ i, I.γ i = 0 → 0 < I.vnp i)
    (hanti : ∀ i, Antitone (I.r i))
    (A : ι → Set (Finset (Fin n))) (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I A xh yh)
    (Sh : ι → Finset (Fin n)) (hSmem : ∀ i, Sh i ∈ A i)
    (hSmax : ∀ i, ∀ S ∈ A i,
      nestWeight I i S * (R I i S - xh) ≤ nestWeight I i (Sh i) * (R I i (Sh i) - xh))
    (α β : ℝ) (hfeas : LP3Feasible I (α * xh) (β • yh)) :
    ∀ Sstar, IsOptimal I Sstar →
      revenue I Sstar ≤ α * revenue I Sh ∧ revenue I Sh ≤ revenue I Sstar := by sorry
