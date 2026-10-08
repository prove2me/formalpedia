-- Prove2me | Theorems.Thm_ConstrNestedLogit_Reduce_eq6
-- name    : ConstrNestedLogit.Reduce.eq6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:33.489217+00:00
-- url     : https://prove2.me/theorems/2493e57e-e320-4aaf-b671-a8fb3a4fe2e9
-- title:
--   §3, p. 13, (6) — $\alpha \hat V_i(\hat R_i - Z^*) \ge (\gamma_i V^*_i + \alpha(1-\gamma_i)\hat V_i)(R^*_i - Z^*)$ when $R^*_i > Z^*$
-- statement:
--   Consider a nested logit instance with $v_0 > 0$, preference weights $v_{ij} > 0$ and dissimilarity parameters $\gamma_i \in (0, 1]$, and feasible assortment sets $\mathcal C_i$ containing the empty assortment $\bar 0$. Let $(S^*_1, \dots, S^*_m)$ be an optimal solution of problem (1) with value $Z^*$, let $u^*_i = \max\{Z^*, \gamma_i Z^* + (1 - \gamma_i) R_i(S^*_i)\}$, let $\alpha \ge 1$, and let assortments $\hat S_i$ satisfy inequality (5),
--   $$\alpha\, V_i(\hat S_i)\big(R_i(\hat S_i) - u^*_i\big) \ge \max_{S_i \in \mathcal C_i} \Big\{ V_i(S_i)\big(R_i(S_i) - u^*_i\big) \Big\} \quad \text{for all } i \in M.$$
--   Write $\hat V_i = V_i(\hat S_i)$, $V^*_i = V_i(S^*_i)$, $\hat R_i = R_i(\hat S_i)$, $R^*_i = R_i(S^*_i)$. Then for every nest $i$ with $R^*_i > Z^*$,
--   $$\alpha\, \hat V_i\,(\hat R_i - Z^*) \ge \big(\gamma_i V^*_i + \alpha (1 - \gamma_i) \hat V_i\big)(R^*_i - Z^*). \tag{6}$$
--
--   This is the first step of the proof of Lemma 3 for the nests where the optimal assortment earns more than $Z^*$ within the nest.
--
--   **Formalization Note** The hypotheses are those of Lemma 3 in this mission (only part of them is needed here). $V_i$ has no within-nest no-purchase weight. $v_0 > 0$ and $v_{ij} > 0$ are added (the paper does not state them; they are the model's standing positivity). $\hat S_i$ is not required to be feasible.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 13, proof of Lemma 3, inequality (6)

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model
import Definitions.Def_ConstrNestedLogit_Reduce_Problems

namespace ConstrNestedLogit.Reduce

open NestedLogitVariants.LP

variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- Inequality (6) of the proof of Lemma 3 (p. 13): in the setting of Lemma 3, for a nest `i`
with `R_i(S*_i) > Z*`,
`α V̂_i (R̂_i − Z*) ≥ (γ_i V*_i + α (1 − γ_i) V̂_i)(R*_i − Z*)`. -/
theorem eq6 (I : Instance ι n) (hvnp : ∀ i, I.vnp i = 0) (hv0 : 0 < I.v0)
    (hv : ∀ i j, 0 < I.v i j) (hγ : ∀ i, 0 < I.γ i ∧ I.γ i ≤ 1)
    (C : ι → Set (Finset (Fin n))) (h0 : ∀ i, ∅ ∈ C i)
    (Sstar : ι → Finset (Fin n)) (hopt : IsOptimal1 I C Sstar)
    (Shat : ι → Finset (Fin n)) (α : ℝ) (hα : 1 ≤ α)
    (h5 : ∀ i, ∀ S ∈ C i, obj7 I i S (uStar I Sstar i) ≤ α * obj7 I i (Shat i) (uStar I Sstar i))
    (i : ι) (hi : revenue I Sstar < R I i (Sstar i)) :
    (I.γ i * V I i (Sstar i) + α * (1 - I.γ i) * V I i (Shat i)) *
        (R I i (Sstar i) - revenue I Sstar) ≤
      α * V I i (Shat i) * (R I i (Shat i) - revenue I Sstar) := by sorry

end ConstrNestedLogit.Reduce
