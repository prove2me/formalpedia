-- Prove2me | Theorems.Thm_AuditAdapt_Supplement_theorem_3_1
-- name    : AuditAdapt.Supplement.theorem_3_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-15T19:36:42.058498+00:00
-- url     : https://prove2.me/theorems/10261e8c-15a7-45b3-be61-d1994969e8fd
-- title:
--   Theorem 3.1, p.3 — pathwise decomposition: $\mathrm{Regret}_T=\sum_t(c_t-\bar c)^\top(z_t-\bar z)+T\bar c^\top(\bar z-z^*)$, last term $\ge0$
-- statement:
--   Let $Z\subset\mathbb R^n$ be convex and compact, let $c_1,\dots,c_T\in\mathbb R^n$ be arbitrary, and let $z_1,\dots,z_T\in Z$ be arbitrary. Let
--
--   $$
--   \bar c=\frac1T\sum_t c_t,\qquad \bar z=\frac1T\sum_t z_t,\qquad z^*\in\arg\min_{z\in Z}\bar c^\top z .
--   $$
--
--   Then
--
--   $$
--   \underbrace{\sum_{t=1}^T c_t^\top z_t-\min_{z\in Z}\sum_{t=1}^T c_t^\top z}_{\mathrm{Regret}_T}
--   =\underbrace{\sum_{t=1}^T(c_t-\bar c)^\top(z_t-\bar z)}_{\widehat C_T}+T\,\bar c^\top(\bar z-z^*),
--   \qquad T\,\bar c^\top(\bar z-z^*)\ge0 .
--   $$
--
--   The regret of any online linear optimization run, against any adversary, is its sample covariance between costs and decisions plus a nonnegative static term; no stochastic assumption is made. It is the accounting identity an auditor computes on a realized path.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ` and $u^\top v$ is `u ⬝ᵥ v`. The minimum is written as the infimum of the image of $Z$ (attained, since $Z$ is compact and nonempty), not as $\sum_t c_t^\top z^*$.
--
--   Differences from the source:
--   - encoding: ℝⁿ with the inner product uᵀv → Fin n → ℝ with dotProduct u ⬝ᵥ v; reason: same vector space; its product topology is the Euclidean topology, so convexity and compactness are unchanged
--   - encoding: min_{z∈Z} Σ_t c_tᵀz → sInf of the image of Z under z ↦ Σ_t c_tᵀz; reason: Z is compact and nonempty (z* ∈ Z), so the infimum is attained and equals the minimum
--   - encoding: z* ∈ arg min_{z∈Z} c̄ᵀz → zstar ∈ Z with c̄ᵀzstar ≤ c̄ᵀy for all y ∈ Z; reason: definition of arg min; any minimizer
--   - generalization: T ≥ 1 rounds (c̄ = (1/T)Σ_t c_t) → any T : ℕ, including T = 0; reason: at T = 0 Lean's 1/0 = 0 and both sides are 0; the T ≥ 1 instances are the source's statement
-- source:
--   Aldridge, Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing Adaptive Policies, STOC 2027 submission (held version, sha256 3f6ad545b0454d8de6836d32bb81359da5022bbc373510a7c75452ab66ec9fc2), Theorem 3.1 (Pathwise decomposition), p.3 (PDF p.3)

import Mathlib

namespace AuditAdapt.Supplement

/-- **Theorem 3.1 (Pathwise decomposition), p.3** (Aldridge, *Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing
Adaptive Policies*, STOC 2027 submission (held version, sha256 3f6ad545…)).
Let `Z ⊂ ℝⁿ` be convex and compact, let `c_1, …, c_T ∈ ℝⁿ` be arbitrary, and let `z_1, …, z_T ∈ Z` be
arbitrary. Let `c̄ = (1/T) Σ_t c_t`, `z̄ = (1/T) Σ_t z_t`, and `z* ∈ arg min_{z∈Z} c̄ᵀz`. Then
`Σ_t c_tᵀz_t − min_{z∈Z} Σ_t c_tᵀz = Σ_t (c_t − c̄)ᵀ(z_t − z̄) + T c̄ᵀ(z̄ − z*)`, and the last term is `≥ 0`.

**Formalization Note** `ℝⁿ` is `Fin n → ℝ` (its product topology is the Euclidean one, so convexity and
compactness are the paper's) and `uᵀv` is `u ⬝ᵥ v`. Rounds are `Fin T`. The minimum
`min_{z∈Z} Σ_t c_tᵀz` is the infimum (`sInf`) of the image of `Z`, which is attained because `Z` is
compact and nonempty (`z* ∈ Z`); it is **not** written as `Σ_t c_tᵀz*`. `z*` is any minimizer of
`c̄ᵀz` over `Z`. For `T = 0`, `1/T = 0` in Lean and both sides are `0`. -/
theorem theorem_3_1 {n T : ℕ} (Z : Set (Fin n → ℝ)) (hZconv : Convex ℝ Z) (hZcpt : IsCompact Z)
    (c z : Fin T → Fin n → ℝ) (hz : ∀ t, z t ∈ Z) (zstar : Fin n → ℝ) (hzstar : zstar ∈ Z)
    (hmin : ∀ y ∈ Z, ((T : ℝ)⁻¹ • ∑ t, c t) ⬝ᵥ zstar ≤ ((T : ℝ)⁻¹ • ∑ t, c t) ⬝ᵥ y) :
    (∑ t, c t ⬝ᵥ z t) - sInf ((fun y => ∑ t, c t ⬝ᵥ y) '' Z) =
        (∑ t, (c t - (T : ℝ)⁻¹ • ∑ t', c t') ⬝ᵥ (z t - (T : ℝ)⁻¹ • ∑ t', z t')) +
          (T : ℝ) * (((T : ℝ)⁻¹ • ∑ t, c t) ⬝ᵥ ((T : ℝ)⁻¹ • ∑ t, z t - zstar)) ∧
      0 ≤ (T : ℝ) * (((T : ℝ)⁻¹ • ∑ t, c t) ⬝ᵥ ((T : ℝ)⁻¹ • ∑ t, z t - zstar)) := by sorry

end AuditAdapt.Supplement
