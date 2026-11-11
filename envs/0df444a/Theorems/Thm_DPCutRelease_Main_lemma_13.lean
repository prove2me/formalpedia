-- Prove2me | Theorems.Thm_DPCutRelease_Main_lemma_13
-- name    : DPCutRelease.Main.lemma_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:12:24.462992+00:00
-- url     : https://prove2.me/theorems/355f0ef4-a8c9-43c2-b138-0f59c8a28677
-- title:
--   Lemma 13 — stability of the log-det regularized SDP maximizer in relative Frobenius norm
-- statement:
--   Let $\lambda>0$, let $A_0$ be any real $n\times n$ matrix, $\xi\in\mathbb R^{\binom n2}$, and $A_1=A_0+\sum_e\xi_eb_eb_e^\top/4$. Let
--   $$X_i=\arg\max_{X\in\mathcal X}\{\langle A_i,X\rangle+\lambda\log\det X\},\qquad i\in\{0,1\}.$$
--   Then
--   $$\big\|X_0^{-1/2}(X_1-X_0)X_1^{-1/2}\big\|_F\le\frac{\sum_e|\xi_e|\sqrt{q_e(X_0)q_e(X_1)}}{\lambda}.$$
--   Additionally, if $\|X_0^{-1/2}(X_1-X_0)X_1^{-1/2}\|_F\le1/2$, then for every $e$, $\frac12q_e(X_1)\le q_e(X_0)\le2q_e(X_1)$. Combined with Lemma 14, it bounds the privacy loss of one Gaussian batch drawn at the SDP optimizer.
--
--   **Formalization Note.** `regArgmax lam A` is the (unique, for $\lambda>0$) maximizer over the elliptope `Elliptope n`; $X^{-1/2}=$ `(CFC.sqrt X)⁻¹`; `edgeMat ξ` $=\sum_e\xi_eb_eb_e^\top/4$; $\langle A,X\rangle=\operatorname{tr}(A^\top X)$.
--
--   Differences from the source:
--   - reading: λ in Eq. (4), positive throughout §3–§5 → hypothesis 0 < lam; reason: the regularization weight of the section; at λ ≤ 0 the maximizer need not be unique
--   - encoding: Xᵢ = arg max over 𝒳 → regArgmax lam Aᵢ (unique maximizer, junk I otherwise); reason: the maximizer exists and is unique for λ > 0, so the junk branch never occurs
-- source:
--   Eliáš et al., Polynomial-Time Differentially Private Synthetic Graph Release with Nearly-Linear Additive Error, arXiv:2611.06670v1, p. 19, Lemma 13

import Mathlib
import Definitions.Def_DPCutRelease_Main_EdgeDP
import Definitions.Def_DPCutRelease_Main_SDP

open MeasureTheory ProbabilityTheory Matrix

namespace DPCutRelease.Main

/-- Lemma 13 (p. 19): for `λ > 0`, any `A₀` and `ξ`, with `A₁ = A₀ + Σ_e ξ_e b_e b_eᵀ/4` and
`X_i = arg max_{X ∈ 𝒳} {⟨A_i, X⟩ + λ log det X}`:
`‖X₀^{−1/2}(X₁ − X₀)X₁^{−1/2}‖_F ≤ Σ_e |ξ_e| √(q_e(X₀) q_e(X₁)) / λ`, and if that norm is at most
`1/2` then `q_e(X₁)/2 ≤ q_e(X₀) ≤ 2 q_e(X₁)` for every `e`. -/
theorem lemma_13 (n : ℕ) (lam : ℝ) (hlam : 0 < lam) (A0 : Mat n) (ξ : EdgeVec n) :
    frobNorm (relErr (regArgmax lam A0) (regArgmax lam (A0 + edgeMat ξ))) ≤
        (∑ e, |ξ e| * Real.sqrt (qe (regArgmax lam A0) e * qe (regArgmax lam (A0 + edgeMat ξ)) e))
          / lam ∧
      (frobNorm (relErr (regArgmax lam A0) (regArgmax lam (A0 + edgeMat ξ))) ≤ 1 / 2 →
        ∀ e, qe (regArgmax lam (A0 + edgeMat ξ)) e / 2 ≤ qe (regArgmax lam A0) e ∧
          qe (regArgmax lam A0) e ≤ 2 * qe (regArgmax lam (A0 + edgeMat ξ)) e) := by sorry

end DPCutRelease.Main
