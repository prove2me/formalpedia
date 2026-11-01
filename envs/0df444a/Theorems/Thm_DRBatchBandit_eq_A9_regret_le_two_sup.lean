-- Prove2me | Theorems.Thm_DRBatchBandit_eq_A9_regret_le_two_sup
-- name    : DRBatchBandit.eq_A9_regret_le_two_sup
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:24:06.433433+00:00
-- url     : https://prove2.me/theorems/b886cac3-78f0-4b76-b781-0cec664cbb57
-- title:
--   (A.9), p.52 — $R_{\mathrm{DRO}}(\hat\pi_{\mathrm{DRO}})\le2\sup_{\pi\in\Pi}|\hat Q_{\mathrm{DRO}}(\pi)-Q_{\mathrm{DRO}}(\pi)|$
-- statement:
--   Let $\Pi$ be a policy class, fix observed data $\{(X_i,A_i,Y_i)\}_{i=1}^n$, and let $\hat\pi_{\mathrm{DRO}}\in\Pi$ maximize $\hat Q_{\mathrm{DRO}}$ over $\Pi$ on these data. Then
--   $$R_{\mathrm{DRO}}(\hat\pi_{\mathrm{DRO}})\le2\sup_{\pi\in\Pi}\big|\hat Q_{\mathrm{DRO}}(\pi)-Q_{\mathrm{DRO}}(\pi)\big|.$$
--
--   This is the first step of the proof of Theorem 2: the robust regret of the learned policy is controlled by the uniform estimation error of the robust value.
--
--   **Formalization Note** The supremum is replaced by an arbitrary bound: for every real $T$ with $|\hat Q_{\mathrm{DRO}}(\pi)-Q_{\mathrm{DRO}}(\pi)|\le T$ for all $\pi\in\Pi$, $R_{\mathrm{DRO}}(\hat\pi_{\mathrm{DRO}})\le2T$. This is equivalent to the printed inequality when the supremum is finite, and avoids a real supremum over $\Pi$.
--
--   Differences from the source:
--   - encoding: actions a¹, …, a^d → Fin d, 0-based; rewards a vector Fin d → ℝ; reason: Lean convention; no instance changes
--   - encoding: 2 sup_{π∈Π} |Q̂_DRO(π) − Q_DRO(π)| → 2T for every real T bounding |Q̂_DRO(π) − Q_DRO(π)| on Π; reason: equivalent when the supremum is finite (otherwise the printed bound is vacuous); avoids a real supremum over Π
--   - generalization: stated inside the proof of Theorem 2, under Assumption 1 → no assumption on the model; reason: the inequality is algebra from the maximality of π̂_DRO; it specializes to the paper's setting
-- source:
--   Si, Zhang, Zhou & Blanchet, Distributionally Robust Batch Contextual Bandits, arXiv:2006.05630v7, proof of Theorem 2, p.52, first display ("Recall RDRO(π̂DRO) = …") and (A.9). PDF sha256 ac485985feb75d33b603f06f5a5d93c52077877db7be11de3d71107c7c374b02

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Setting
import Definitions.Def_DRBatchBandit_RobustValue
import Definitions.Def_DRBatchBandit_Estimator

namespace DRBatchBandit

open OfflinePolicyLearning.Regret

/-- (A.9), proof of Theorem 2 (Si, Zhang, Zhou & Blanchet, arXiv:2006.05630v7, p.52): for the
maximizer `π̂_DRO` of `Q̂_DRO` over `Π` on a data set,
`R_DRO(π̂_DRO) ≤ 2 sup_{π ∈ Π} |Q̂_DRO(π) − Q_DRO(π)|`.

**Formalization Note.** Stated for every bound `T` on `|Q̂_DRO(π) − Q_DRO(π)|` over `Π`, which is
equivalent to the printed form with `T` the supremum and avoids a real supremum over `Π`. The
data set is any `D : Fin n → Obs X d`; no assumption of the paper is needed. -/
theorem eq_A9_regret_le_two_sup {X : Type*} [MeasurableSpace X] {d : ℕ} (M : Model X d) (δ : ℝ)
    (Pol : Set (X → Fin d)) {n : ℕ} (D : Fin n → Obs X d) (πhat : X → Fin d)
    (hmem : πhat ∈ Pol) (hmax : ∀ π ∈ Pol, QhatDRO M δ D π ≤ QhatDRO M δ D πhat)
    (T : ℝ) (hT : ∀ π ∈ Pol, |QhatDRO M δ D π - QDRO M δ π| ≤ T) :
    RDRO M δ Pol πhat ≤ 2 * T := by sorry

end DRBatchBandit
