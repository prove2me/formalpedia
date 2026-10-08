-- Prove2me | Theorems.Thm_ConstrNestedLogit_Reduce_theorem_4
-- name    : ConstrNestedLogit.Reduce.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:04:03.377441+00:00
-- url     : https://prove2.me/theorems/8810b75b-d806-4560-b247-6e15bc9b22be
-- title:
--   Theorem 4 (p. 15) — candidates containing an α-approximate solution of (7) for every $u \ge 0$ yield an assortment with $\alpha\,\Pi \ge Z^*$
-- statement:
--   Consider a nested logit instance with nests $M$, products $N = \{1, \dots, n\}$, no-purchase weight $v_0 > 0$, preference weights $v_{ij} > 0$, arbitrary revenues $r_{ij}$ and dissimilarity parameters $\gamma_i \in (0, 1]$. For each nest $i$ let $\mathcal C_i$ be a set of feasible assortments containing the empty assortment $\bar 0$, and let $(S^*_1, \dots, S^*_m)$ be an optimal solution of problem (1) with value
--   $$Z^* = \max_{(S_1, \dots, S_m) \in \mathcal C_1 \times \dots \times \mathcal C_m} \Pi(S_1, \dots, S_m).$$
--   Let $\alpha \ge 1$. For each nest $i$ let $\{A^t_i : t \in \mathcal T_i\} \subseteq \mathcal C_i$ be a collection of candidate assortments that, for every $u \ge 0$, contains an $\alpha$-approximate solution of
--   $$\max_{S_i \in \mathcal C_i} \Big\{ V_i(S_i)\big(R_i(S_i) - u\big) \Big\}, \tag{7}$$
--   that is, some $A^t_i$ with $\alpha\, V_i(A^t_i)(R_i(A^t_i) - u) \ge V_i(S_i)(R_i(S_i) - u)$ for every $S_i \in \mathcal C_i$. Then there is an assortment $(\hat S_1, \dots, \hat S_m)$ with $\hat S_i \in \{A^t_i : t \in \mathcal T_i\}$ for every $i$ and
--   $$\alpha\, \Pi(\hat S_1, \dots, \hat S_m) \ge Z^*.$$
--
--   The collection is fixed first and must work for every threshold $u \ge 0$. The theorem reduces the constrained assortment problem over all nests to the single-nest problems (7), whose objective is linear in the assortment; combined with the linear program of Theorem 2, it turns a small candidate collection into an $\alpha$-approximate assortment.
--
--   **Formalization Note** $V_i(S_i) = \sum_{j \in S_i} v_{ij}$ (the published model with zero within-nest no-purchase weight), $R_i(\bar 0) = 0$, powers are `Real.rpow`, assortments are finite sets of products indexed from $0$. The collection is a set `A i` of assortments (the index set $\mathcal T_i$ is not named, and no finiteness is required). Added hypotheses: $v_0 > 0$, $v_{ij} > 0$, $\bar 0 \in \mathcal C_i$ and $\alpha \ge 1$ (the paper's standing context for Lemma 3). $A_i \subseteq \mathcal C_i$ is the paper's ("All of the assortments in the collection are feasible", p. 11).
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 15, Theorem 4

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model
import Definitions.Def_ConstrNestedLogit_Reduce_Problems

namespace ConstrNestedLogit.Reduce

open NestedLogitVariants.LP

variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- Theorem 4 (p. 15): if, for every nest `i`, the candidate collection `A_i ⊆ C_i` contains an
`α`-approximate solution of problem (7) for every `u ≥ 0`, then some assortment
`(Ŝ_1, …, Ŝ_m)` with `Ŝ_i ∈ A_i` satisfies `α Π(Ŝ_1, …, Ŝ_m) ≥ Z*`. -/
theorem theorem_4 (I : Instance ι n) (hvnp : ∀ i, I.vnp i = 0) (hv0 : 0 < I.v0)
    (hv : ∀ i j, 0 < I.v i j) (hγ : ∀ i, 0 < I.γ i ∧ I.γ i ≤ 1)
    (C : ι → Set (Finset (Fin n))) (h0 : ∀ i, ∅ ∈ C i)
    (Sstar : ι → Finset (Fin n)) (hopt : IsOptimal1 I C Sstar)
    (α : ℝ) (hα : 1 ≤ α)
    (A : ι → Set (Finset (Fin n))) (hAC : ∀ i, A i ⊆ C i)
    (hA : ∀ i, ∀ u : ℝ, 0 ≤ u → ∃ S ∈ A i, IsApproxSol7 I C i α u S) :
    ∃ Shat : ι → Finset (Fin n),
      (∀ i, Shat i ∈ A i) ∧ revenue I Sstar ≤ α * revenue I Shat := by sorry

end ConstrNestedLogit.Reduce
