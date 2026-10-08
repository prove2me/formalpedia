-- Prove2me | Theorems.Thm_ConstrNestedLogit_Reduce_lemma_3
-- name    : ConstrNestedLogit.Reduce.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:03:53.920261+00:00
-- url     : https://prove2.me/theorems/ff6a17ef-ce8e-4327-8b62-2a1ec241df66
-- title:
--   Lemma 3 (p. 13) — assortments satisfying (5) at $u^*_i$ for some $\alpha \ge 1$ earn at least $Z^*/\alpha$
-- statement:
--   Consider a nested logit instance with no-purchase weight $v_0 > 0$, preference weights $v_{ij} > 0$ and dissimilarity parameters $\gamma_i \in (0, 1]$, and for each nest $i$ a set $\mathcal C_i$ of feasible assortments containing the empty assortment $\bar 0$. Let $(S^*_1, \dots, S^*_m)$ be an optimal solution of problem (1),
--   $$Z^* = \max_{(S_1, \dots, S_m) \in \mathcal C_1 \times \dots \times \mathcal C_m} \Pi(S_1, \dots, S_m),$$
--   and set $u^*_i = \max\{Z^*, \gamma_i Z^* + (1 - \gamma_i) R_i(S^*_i)\}$ for all $i \in M$. If $\alpha \ge 1$ and the assortments $\hat S_i$, $i \in M$, satisfy
--   $$\alpha\, V_i(\hat S_i)\big(R_i(\hat S_i) - u^*_i\big) \ge \max_{S_i \in \mathcal C_i} \Big\{ V_i(S_i)\big(R_i(S_i) - u^*_i\big) \Big\}, \tag{5}$$
--   then
--   $$\alpha\, \Pi(\hat S_1, \dots, \hat S_m) \ge Z^*.$$
--
--   Lemma 3 says that solving each nest's linear-in-$S_i$ problem at the right threshold within a factor $\alpha$ is enough for a factor-$\alpha$ assortment overall; Theorem 4 removes the dependence on the unknown threshold $u^*_i$.
--
--   **Formalization Note** $V_i(S_i) = \sum_{j \in S_i} v_{ij}$ (the published model with its within-nest no-purchase weight set to zero), $R_i(\bar 0) = 0$, powers are `Real.rpow`. Added hypotheses: $v_0 > 0$ and $v_{ij} > 0$ (standing positivity of the model, not restated in the paper), and $\bar 0 \in \mathcal C_i$ (the proof evaluates (5) at $S_i = \bar 0$; it holds for the paper's cardinality and space constraints). The maximum in (5) is written as "for every $S_i \in \mathcal C_i$". As in the paper, $\hat S_i$ need not be feasible. Revenues $r_{ij}$ are arbitrary reals.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 13, Lemma 3

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model
import Definitions.Def_ConstrNestedLogit_Reduce_Problems

namespace ConstrNestedLogit.Reduce

open NestedLogitVariants.LP

variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- Lemma 3 (p. 13): if `(S*_1, …, S*_m)` is optimal for problem (1) with value `Z*` and the
assortments `Ŝ_i` satisfy (5) at `u*_i = max{Z*, γ_i Z* + (1 − γ_i) R_i(S*_i)}` for some
`α ≥ 1`, then `α Π(Ŝ_1, …, Ŝ_m) ≥ Z*`. -/
theorem lemma_3 (I : Instance ι n) (hvnp : ∀ i, I.vnp i = 0) (hv0 : 0 < I.v0)
    (hv : ∀ i j, 0 < I.v i j) (hγ : ∀ i, 0 < I.γ i ∧ I.γ i ≤ 1)
    (C : ι → Set (Finset (Fin n))) (h0 : ∀ i, ∅ ∈ C i)
    (Sstar : ι → Finset (Fin n)) (hopt : IsOptimal1 I C Sstar)
    (Shat : ι → Finset (Fin n)) (α : ℝ) (hα : 1 ≤ α)
    (h5 : ∀ i, ∀ S ∈ C i, obj7 I i S (uStar I Sstar i) ≤ α * obj7 I i (Shat i) (uStar I Sstar i)) :
    revenue I Sstar ≤ α * revenue I Shat := by sorry

end ConstrNestedLogit.Reduce
