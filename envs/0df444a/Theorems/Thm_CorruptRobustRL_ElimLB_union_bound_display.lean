-- Prove2me | Theorems.Thm_CorruptRobustRL_ElimLB_union_bound_display
-- name    : CorruptRobustRL.ElimLB.union_bound_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:34.362059+00:00
-- url     : https://prove2.me/theorems/b7ae4a53-6e22-4865-8403-efe4c64d4273
-- title:
--   Display, p. 39 — P^{ℳ₀}[⋂(ℰ^combi_k)^c ∩ ⋂ℰ^adm_k] ≥ P^{ℳ₀}[⋂ℰ^adm_k] − Σ_k P^{ℳ₀}[ℰ^combi_k ∩ ℰ^adm_k]
-- statement:
--   Let $H\ge1$, $A\ge2$, and run any uniformly action-eliminating algorithm for $K$ episodes on the all-zero combination-lock instance $\mathcal M_0$. Then
--
--   $$
--   \mathbb P^{\mathcal M_0}\Bigl[\bigcap_{k=1}^K(\mathcal E^{\mathrm{combi}}_k)^c\cap\bigcap_{k=1}^K\mathcal E^{\mathrm{adm}}_k\Bigr]\ \ge\ \mathbb P^{\mathcal M_0}\Bigl[\bigcap_{k=1}^K\mathcal E^{\mathrm{adm}}_k\Bigr]-\sum_{k=1}^K\mathbb P^{\mathcal M_0}\bigl[\mathcal E^{\mathrm{combi}}_k\cap\mathcal E^{\mathrm{adm}}_k\bigr].
--   $$
--
--   This is Boole's law and a union bound; it is the third line of the paper's display on p. 39.
--
--   **Formalization Note** Probabilities are converted to real numbers, so the difference is an honest real subtraction. The paper's last line, with the conditional probabilities $\mathbb P^{\mathcal M_0}[\mathcal E^{\mathrm{combi}}_k\mid\mathcal E^{\mathrm{adm}}_k]$, follows from this one because $\mathbb P[E\cap F]\le\mathbb P[E\mid F]$.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 39, App. A, union-bound display (third line)

import Mathlib
import Definitions.Def_CorruptRobustRL_ElimLB_MDP
import Definitions.Def_CorruptRobustRL_ElimLB_Setting
import Definitions.Def_CorruptRobustRL_ElimLB_ComboLock

namespace CorruptRobustRL.ElimLB

/-- Boole's law and the union bound, arXiv:1911.08689v4, App. A, p. 39 (third line of the
display): `P^{ℳ₀}[⋂_k (ℰ^combi_k)^c ∩ ⋂_k ℰ^adm_k] ≥ P^{ℳ₀}[⋂_k ℰ^adm_k] − Σ_k P^{ℳ₀}[ℰ^combi_k ∩ ℰ^adm_k]`,
in real numbers. -/
theorem union_bound_display (H A : ℕ) [NeZero A] (hH : 1 ≤ H) (hA : 2 ≤ A)
    (L : Learner (Fin (H + 1)) (Fin A) H) (K : ℕ) :
    ((runLaw (comboLock0 H A) L K).toOuterMeasure {run | ∀ k < K, admEv k run}).toReal -
        ∑ k ∈ Finset.range K,
          ((runLaw (comboLock0 H A) L K).toOuterMeasure
            ({run | combi k run} ∩ {run | admEv k run})).toReal ≤
      ((runLaw (comboLock0 H A) L K).toOuterMeasure
        ({run | ∀ k < K, ¬ combi k run} ∩ {run | ∀ k < K, admEv k run})).toReal := by sorry

end CorruptRobustRL.ElimLB
