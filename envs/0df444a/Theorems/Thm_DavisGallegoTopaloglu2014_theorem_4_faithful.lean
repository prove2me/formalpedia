-- Prove2me | Theorems.Thm_DavisGallegoTopaloglu2014_theorem_4_faithful
-- name    : DavisGallegoTopaloglu2014.theorem_4_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:30:00.714243+00:00
-- url     : https://prove2.me/theorems/93acc1e5-1191-44ff-9c30-d92a38c0bedb
-- title:
--   Theorem 4 with zero preference weights allowed (nested-by-revenue optimality)
-- statement:
--   Consider the nested logit model with nests $M$ and products $N = \{1, \dots, n\}$ in every nest, revenues $r_{ij} \ge 0$ ordered so that $r_{i1} \ge \dots \ge r_{in}$, preference weights $v_{ij} \ge 0$ (zero weights allowed), no-purchase weights $v_0 \ge 0$ and $v_{i0} = 0$ for every nest (fully captured nests), and dissimilarity parameters $0 < \gamma_i \le 1$. Write $V_i(S) = \sum_{j \in S} v_{ij}$, $R_i(S) = \sum_{j \in S} r_{ij} v_{ij} / V_i(S)$ with $R_i(\emptyset) = 0$, and
--   $$\Pi(S_1, \dots, S_m) = \frac{\sum_{i \in M} V_i(S_i)^{\gamma_i} R_i(S_i)}{v_0 + \sum_{i \in M} V_i(S_i)^{\gamma_i}}.$$
--   Let $N_{ij} = \{1, \dots, j\}$ for $j = 0, \dots, n$. Then there is an assortment $(S^*_1, \dots, S^*_m)$ maximizing $\Pi$ such that
--   $$S^*_i = N_{ij_i} \quad \text{for some } j_i \in \{0, \dots, n\}, \qquad \text{for every } i \in M.$$
--
--   This is Theorem 4 of Davis, Gallego and Topaloglu (2014) as stated in the paper, whose model admits zero-weight products (they pad nests to a common size $n$). The platform theorem NestedLogitVariants.Competitive.theorem_4 proves it under the extra assumption that every $v_{ij}$ is strictly positive.
--
--   **Formalization Note** Products are indexed $0, \dots, n-1$ and $N_{ij}$ is `nbr n j`. Division is total ($x/0 = 0$). The assumption $\gamma_i > 0$ is kept: at $\gamma_i = 0$ the real power $0^0 = 1$ would give the empty fully captured nest positive weight, a case the paper does not specify.
-- source:
--   Davis, Gallego, Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, Operations Research 62(2), 2014, doi:10.1287/opre.2014.1256, p. 15, Theorem 4 (model p. 7, standing assumptions §3 pp. 13-14)

import Mathlib
import Definitions.Def_NestedLogitVariants_Competitive_Model

open NestedLogitVariants.Competitive

theorem DavisGallegoTopaloglu2014.theorem_4_faithful {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.Competitive.Instance ι n)
    (hv0 : 0 ≤ I.v0) (hv : ∀ i j, 0 ≤ I.v i j) (hr : ∀ i j, 0 ≤ I.r i j)
    (hγpos : ∀ i, 0 < I.γ i) (hanti : ∀ i, Antitone (I.r i))
    (hγ : ∀ i, I.γ i ≤ 1) (hfc : ∀ i, I.vnp i = 0) :
    ∃ S : ι → Finset (Fin n), IsOptimal I S ∧ ∀ i, ∃ j ≤ n, S i = nbr n j := by sorry
