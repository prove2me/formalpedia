-- Prove2me | Theorems.Thm_DavisGallegoTopaloglu2014_theorem_7_faithful
-- name    : DavisGallegoTopaloglu2014.theorem_7_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:30:16.384849+00:00
-- url     : https://prove2.me/theorems/c26a3b2d-f950-4497-aedf-801f9783f40e
-- title:
--   Theorem 7 with zero weights and zero lower revenues allowed (factor (6) for nested-by-revenue assortments)
-- statement:
--   Consider the nested logit model with nests $M$ and products $N = \{1, \dots, n\}$, $n \ge 2$, in every nest, revenues $r_{ij} \ge 0$ ordered so that $r_{i1} \ge \dots \ge r_{in}$, preference weights $v_{ij} \ge 0$, no-purchase weight $v_0 \ge 0$, fully captured nests ($v_{i0} = 0$), and dissimilarity parameters $\gamma_i > 0$ with $\gamma_i > 1$ for some nest. Assume $v_{i1} > 0$ and $r_{i1} > 0$ in every nest, so that every $R_i(N_{ij})$, $j \ge 1$, is positive. Let $N_{ij} = \{1, \dots, j\}$, let $(\hat x, \hat y)$ be an optimal solution of the linear program
--   $$\min x \quad \text{s.t.} \quad v_0 x \ge \sum_{i \in M} y_i, \qquad y_i \ge V_i(N_{ij})^{\gamma_i} \big(R_i(N_{ij}) - x\big) \quad \forall i \in M,\ j = 0, \dots, n,$$
--   and let
--   $$\alpha = \max_{i \in M,\ j = 2, \dots, n} \Big\{ \frac{R_i(N_{i,j-1})}{R_i(N_{ij})} \wedge \frac{R_i(N_{ij})}{R_i(N_{i,j-1})} \frac{V_i(N_{ij})^{\gamma_i}}{V_i(N_{i,j-1})^{\gamma_i}} \Big\}.$$
--   Then $(\alpha \hat x, \alpha \hat y)$ satisfies $v_0 \alpha \hat x \ge \sum_i \alpha \hat y_i$ and $\alpha \hat y_i \ge V_i(S)^{\gamma_i}(R_i(S) - \alpha \hat x)$ for every nest $i$ and every $S \subseteq N$.
--
--   This is Theorem 7 of Davis, Gallego and Topaloglu (2014), with only the positivity the factor (6) itself needs. The platform theorem NestedLogitVariants.Synergistic.theorem_7 proves it assuming every $r_{ij} > 0$ and every $v_{ij} > 0$.
--
--   **Formalization Note** Products are indexed from $0$, so $v_{i1}$, $r_{i1}$ are `I.v i ⟨0, _⟩`, `I.r i ⟨0, _⟩`; $N_{ij}$ is `nbr n j`. Division is total ($x/0 = 0$), but no denominator of (6) vanishes under the hypotheses.
-- source:
--   Davis, Gallego, Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, Operations Research 62(2), 2014, doi:10.1287/opre.2014.1256, p. 21, Theorem 7 (factor (6) p. 19; standing assumptions §4 p. 16; proof Appendix A.1 pp. 41-43)

import Mathlib
import Definitions.Def_NestedLogitVariants_Synergistic_Model
import Definitions.Def_NestedLogitVariants_Synergistic_Factor

open NestedLogitVariants.Synergistic

theorem DavisGallegoTopaloglu2014.theorem_7_faithful {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.Synergistic.Instance ι n)
    (hv0 : 0 ≤ I.v0) (hv : ∀ i j, 0 ≤ I.v i j) (hrnn : ∀ i j, 0 ≤ I.r i j)
    (hγpos : ∀ i, 0 < I.γ i) (hanti : ∀ i, Antitone (I.r i))
    (hfc : ∀ i, I.vnp i = 0) (hsyn : ∃ i, 1 < I.γ i) (hn : 2 ≤ n)
    (hv1 : ∀ i, 0 < I.v i ⟨0, by omega⟩) (hr1 : ∀ i, 0 < I.r i ⟨0, by omega⟩)
    (α : ℝ) (hα : IsGreatest (alphaTerms I) α)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (fun _ => {S | ∃ j ≤ n, S = nbr n j}) xh yh) :
    LP3Feasible I (α * xh) (α • yh) := by sorry
