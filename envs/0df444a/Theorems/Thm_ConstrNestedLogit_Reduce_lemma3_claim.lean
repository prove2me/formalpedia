-- Prove2me | Theorems.Thm_ConstrNestedLogit_Reduce_lemma3_claim
-- name    : ConstrNestedLogit.Reduce.lemma3_claim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:03:55.175264+00:00
-- url     : https://prove2.me/theorems/358054e5-d5cd-47dd-a736-243ba956d9ef
-- title:
--   §3, pp. 13–14 — claim of Lemma 3's proof: $\alpha \hat V_i^{\gamma_i}(\hat R_i - Z^*) \ge (V^*_i)^{\gamma_i}(R^*_i - Z^*)$ for all nests
-- statement:
--   Consider a nested logit instance with $v_0 > 0$, preference weights $v_{ij} > 0$ and dissimilarity parameters $\gamma_i \in (0, 1]$, and feasible assortment sets $\mathcal C_i$ that contain the empty assortment $\bar 0$. Let $(S^*_1, \dots, S^*_m)$ be an optimal solution of problem (1) with value $Z^*$, set $u^*_i = \max\{Z^*, \gamma_i Z^* + (1 - \gamma_i) R_i(S^*_i)\}$, let $\alpha \ge 1$, and let the assortments $\hat S_i$ satisfy
--   $$\alpha\, V_i(\hat S_i)\big(R_i(\hat S_i) - u^*_i\big) \ge V_i(S_i)\big(R_i(S_i) - u^*_i\big) \quad \text{for all } S_i \in \mathcal C_i,\ i \in M. \tag{5}$$
--   Then for every nest $i \in M$,
--   $$\alpha\, V_i(\hat S_i)^{\gamma_i}\big(R_i(\hat S_i) - Z^*\big) \ge V_i(S^*_i)^{\gamma_i}\big(R_i(S^*_i) - Z^*\big).$$
--
--   Summed over the nests and combined with $v_0 Z^* = \sum_i V_i(S^*_i)^{\gamma_i}(R_i(S^*_i) - Z^*)$, this claim gives Lemma 3.
--
--   **Formalization Note** $V_i(S_i) = \sum_{j \in S_i} v_{ij}$ (no within-nest no-purchase weight), $R_i(\bar 0) = 0$, and powers are `Real.rpow`. $v_0 > 0$ and $v_{ij} > 0$ are added standing positivity; $\bar 0 \in \mathcal C_i$ is added because the proof evaluates (5) at $S_i = \bar 0$ ("$\bar 0$ is a feasible ... solution"). $\hat S_i$ is not required to be feasible, as in the paper.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, pp. 13–14, proof of Lemma 3 (the claim)

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model
import Definitions.Def_ConstrNestedLogit_Reduce_Problems

namespace ConstrNestedLogit.Reduce

open NestedLogitVariants.LP

variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- The claim in the proof of Lemma 3 (pp. 13–14): in the setting of Lemma 3, for every nest `i`,
`α V_i(Ŝ_i)^{γ_i} (R_i(Ŝ_i) − Z*) ≥ V_i(S*_i)^{γ_i} (R_i(S*_i) − Z*)`. -/
theorem lemma3_claim (I : Instance ι n) (hvnp : ∀ i, I.vnp i = 0) (hv0 : 0 < I.v0)
    (hv : ∀ i j, 0 < I.v i j) (hγ : ∀ i, 0 < I.γ i ∧ I.γ i ≤ 1)
    (C : ι → Set (Finset (Fin n))) (h0 : ∀ i, ∅ ∈ C i)
    (Sstar : ι → Finset (Fin n)) (hopt : IsOptimal1 I C Sstar)
    (Shat : ι → Finset (Fin n)) (α : ℝ) (hα : 1 ≤ α)
    (h5 : ∀ i, ∀ S ∈ C i, obj7 I i S (uStar I Sstar i) ≤ α * obj7 I i (Shat i) (uStar I Sstar i)) :
    ∀ i, nestWeight I i (Sstar i) * (R I i (Sstar i) - revenue I Sstar) ≤
      α * nestWeight I i (Shat i) * (R I i (Shat i) - revenue I Sstar) := by sorry

end ConstrNestedLogit.Reduce
