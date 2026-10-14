-- Prove2me | Theorems.Thm_CorruptRobustRL_ElimLB_eqA2_combination_probability
-- name    : CorruptRobustRL.ElimLB.eqA2_combination_probability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:51:58.273772+00:00
-- url     : https://prove2.me/theorems/83267f1c-dcd6-4bfb-95c0-378908365d2c
-- title:
--   (A.2), p. 38 — P[ℰ^combi_k | ℰ^{no elim}_k] = A^{−H} under both ℳ and ℳ₀ (multiplied form)
-- statement:
--   Let $H\ge1$, $A\ge2$, and run any uniformly action-eliminating algorithm for $K$ episodes on the combination-lock instance $\mathcal M$ or $\mathcal M_0$. For every episode $k\le K$,
--
--   $$
--   \mathbb P^{\mathcal M}\bigl[\mathcal E^{\mathrm{combi}}_k\cap\mathcal E^{\mathrm{no\,elim}}_k\bigr]=A^{-H}\,\mathbb P^{\mathcal M}\bigl[\mathcal E^{\mathrm{no\,elim}}_k\bigr],\qquad
--   \mathbb P^{\mathcal M_0}\bigl[\mathcal E^{\mathrm{combi}}_k\cap\mathcal E^{\mathrm{no\,elim}}_k\bigr]=A^{-H}\,\mathbb P^{\mathcal M_0}\bigl[\mathcal E^{\mathrm{no\,elim}}_k\bigr].
--   $$
--
--   When no action is eliminated, the uniformly-at-random policy chooses each $a_{k;h}$ independently and uniformly from $\mathcal A$, so the correct combination has probability $A^{-H}$.
--
--   **Formalization Note** The paper writes the conditional probability $\mathbb P[\mathcal E^{\mathrm{combi}}_k\mid\mathcal E^{\mathrm{no\,elim}}_k]=A^{-H}$; the multiplied form above is equivalent when $\mathbb P[\mathcal E^{\mathrm{no\,elim}}_k]>0$ and stays meaningful otherwise. Episodes are 0-based ($k<K$), and probabilities are in $[0,\infty]$.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 38, App. A, observation 2, display (A.2)

import Mathlib
import Definitions.Def_CorruptRobustRL_ElimLB_MDP
import Definitions.Def_CorruptRobustRL_ElimLB_Setting
import Definitions.Def_CorruptRobustRL_ElimLB_ComboLock

namespace CorruptRobustRL.ElimLB

/-- (A.2), arXiv:1911.08689v4, App. A, p. 38, in multiplied form: for every episode `k < K`,
`P[ℰ^combi_k ∩ ℰ^{no elim}_k] = A^{-H} · P[ℰ^{no elim}_k]` under both `ℳ` and `ℳ₀`. -/
theorem eqA2_combination_probability (H A : ℕ) [NeZero A] (hH : 1 ≤ H) (hA : 2 ≤ A)
    (L : Learner (Fin (H + 1)) (Fin A) H) (K k : ℕ) (hk : k < K) :
    (runLaw (comboLock H A) L K).toOuterMeasure
        ({run | combi k run} ∩ {run | noElimEv k run}) =
      ((A : ENNReal)⁻¹) ^ H * (runLaw (comboLock H A) L K).toOuterMeasure {run | noElimEv k run} ∧
    (runLaw (comboLock0 H A) L K).toOuterMeasure
        ({run | combi k run} ∩ {run | noElimEv k run}) =
      ((A : ENNReal)⁻¹) ^ H * (runLaw (comboLock0 H A) L K).toOuterMeasure {run | noElimEv k run} := by sorry

end CorruptRobustRL.ElimLB
