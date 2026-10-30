-- Prove2me | Theorems.Thm_DDROCS_supportFn_UCS
-- name    : DDROCS.supportFn_UCS
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:33:50.670796+00:00
-- url     : https://prove2.me/theorems/0e3cd7a8-9a22-445f-95f8-4c631a31d44f
-- title:
--   Proof of Theorem 10: the support function of $\mathcal U^{CS}_\epsilon$ is the right-hand side of (34)
-- statement:
--   Let $\hat\mu \in \mathbb R^d$, $\hat\Sigma \in \mathbb R^{d\times d}$, $\Gamma_1 \ge 0$, $\Gamma_2 \in \mathbb R$, and let $C \in \mathbb R^{d\times d}$ satisfy $C^\top C = \hat\Sigma + \Gamma_2 I$. Then for every $0<\epsilon<1$ and every $v \in \mathbb R^d$, the support function of the set $\mathcal U^{CS}_\epsilon$ of (35) built from $\hat\mu$, $\Gamma_1$, $C$ is
--
--   $$
--   \delta^*(v \mid \mathcal U^{CS}_\epsilon) \;=\; \sup_{u \in \mathcal U^{CS}_\epsilon} v^\top u \;=\; \hat\mu^\top v + \Gamma_1\|v\|_2 + \sqrt{\frac{1-\epsilon}{\epsilon}}\,\sqrt{v^\top(\hat\Sigma + \Gamma_2 I)v}.
--   $$
--
--   This identifies the set whose support function is the bound (34), i.e. Step 3 of the schema for $\mathcal P^{CS}$. It is the content of the "Moreover" clause of Theorem 10 and, with Theorem 3(a) and (34), gives its first clause.
--
--   Differences from the source:
--   - generalization: µ̂ the sample mean, Σ̂ the sample covariance, Γ^B_1, Γ^B_2 the bootstrapped thresholds, C a Cholesky factor of Σ̂ + Γ^B_2 I → arbitrary µ̂, Σ̂, Γ2, any Γ1 ≥ 0 and any C with CᵀC = Σ̂ + Γ2 I; reason: the identity holds for any such data and specializes to the paper's choices (a Cholesky factor satisfies CᵀC = Σ̂ + Γ2 I)
--   - encoding: δ∗(v| U^CS_ϵ) = sup_{u∈U^CS_ϵ} vᵀu given by the right-hand side of (34) → IsLUB of {⟪v, u⟫ : u ∈ UCS} at the right-hand side; reason: the least upper bound of the set is the supremum, without Lean's junk value for a real sSup
--   - encoding: threshold Γ1 (a norm bound) → hypothesis 0 ≤ Γ1; reason: every threshold of the paper is a norm bound, hence nonnegative; a negative Γ1 would make (35) empty
--   - reading: ‖y‖, ‖w‖ in (35) → Euclidean norms; reason: (34) has ‖v‖2 and the Cauchy–Schwarz argument of the proof is for the Euclidean norm
--   - encoding: level ϵ with 0 < ϵ < 1 (the family {U^CS_ϵ : 0 < ϵ < 1}) → hypotheses 0 < ε and ε < 1; reason: the paper's range written as binders
-- source:
--   Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, proof of Theorem 10, p. ec8 (PDF p. 46), unnumbered; Theorem 10 "Moreover" clause, p. 25

import Mathlib
import Definitions.Def_DDROCS_UCS
open InnerProductSpace Matrix

namespace DDROCS

/-- **Support function of the mean–covariance set (35) is the right-hand side of (34).**
Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, proof of
Theorem 10, p. ec8 (PDF p. 46), unnumbered: "By Theorem 3, it suffices to show that
`δ∗(v| U^CS_ϵ)` is given by (34), which follows immediately from two applications of the
Cauchy-Schwartz inequality." The same fact is the "Moreover" clause of Theorem 10, p. 25.

If `0 ≤ Γ₁` and `CᵀC = Σ̂ + Γ₂ I`, then for every `0 < ε < 1` and every `v` the supremum of
`vᵀu` over `u ∈ U^CS_ε` has least upper bound
`µ̂ᵀv + Γ₁‖v‖₂ + √((1 − ε)/ε) √(vᵀ(Σ̂ + Γ₂ I)v)`.

**Formalization Note.** `δ∗(v| U^CS_ε)` is stated as `IsLUB` of `{⟪v, u⟫ : u ∈ U^CS_ε}`, so no
junk value of a real supremum is involved. `µ̂`, `Σ̂`, `Γ₂` are arbitrary and `C` is any matrix with
`CᵀC = Σ̂ + Γ₂ I` (a Cholesky factor is one). `0 ≤ Γ₁` is required because a negative threshold
makes (35) empty; every threshold of the paper is a norm bound, hence nonnegative. `vᵀAv` is
`∑ i, ∑ j, v i * A i j * v j`. -/
theorem supportFn_UCS {d : ℕ} (μhat : EuclideanSpace ℝ (Fin d))
    (Sigmahat : Matrix (Fin d) (Fin d) ℝ) (Γ₁ Γ₂ : ℝ) (hΓ₁ : 0 ≤ Γ₁)
    (C : Matrix (Fin d) (Fin d) ℝ)
    (hC : Cᵀ * C = Sigmahat + Γ₂ • (1 : Matrix (Fin d) (Fin d) ℝ))
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (v : EuclideanSpace ℝ (Fin d)) :
    IsLUB ((fun u => ⟪v, u⟫_ℝ) '' UCS μhat Γ₁ C ε)
      (⟪μhat, v⟫_ℝ + Γ₁ * ‖v‖ + Real.sqrt ((1 - ε) / ε) *
        Real.sqrt (∑ i, ∑ j, v i * (Sigmahat + Γ₂ • (1 : Matrix (Fin d) (Fin d) ℝ)) i j * v j)) := by sorry

end DDROCS
