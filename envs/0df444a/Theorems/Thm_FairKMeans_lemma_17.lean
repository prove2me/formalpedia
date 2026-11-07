-- Prove2me | Theorems.Thm_FairKMeans_lemma_17
-- name    : FairKMeans.lemma_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:32:12.559196+00:00
-- url     : https://prove2.me/theorems/488625a6-a798-41af-9d2a-f906b39b5fed
-- title:
--   Lemma 17 — mixing identity: $C$ and $\nu$ are affine and $\Psi$ is quadratic along mixtures
-- statement:
--   Fix $\theta\in[0,1]$, $\rho\ge 1$, $\lambda=\rho/(1+\rho)$, and two relaxed solutions $(T_1,\phi_{T_1})$, $(T_2,\phi_{T_2})$, and let $(T_\theta,\phi_{T_\theta})$ be their $\theta$-mixture, $T_\theta=T_1\uplus T_2$, $\phi_{T_\theta}=(1-\theta)\phi_{T_1}\oplus\theta\phi_{T_2}$. Then
--
--   $$C_{T_\theta}=(1-\theta)C_{T_1}+\theta C_{T_2},\qquad \nu_p(\phi_{T_\theta})=(1-\theta)\nu_p(\phi_{T_1})+\theta\,\nu_p(\phi_{T_2})\ \ (p\in P), \tag{24}$$
--
--   and, with $L$ the linearized cost at $(T_1,\phi_{T_1})$,
--
--   $$\Psi(\phi_{T_\theta})=\Psi(\phi_{T_1})-\theta\big(L(\phi_{T_1})-L(\phi_{T_2})\big)+\lambda\theta^2\sum_{p\in P}\|\nu_p(\phi_{T_1})-\nu_p(\phi_{T_2})\|^2. \tag{25}$$
--
--   The identity justifies the Frank–Wolfe steps of Algorithm 1.
--
--   Differences from the source:
--   - encoding: π(t) of a zero column (undefined) → Lean's 0⁻¹ • 0 = 0, always multiplied by the weight 0; reason: Lean convention; no sum changes
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Lemma 17, (24)–(25), p.22 (PDF p.24)

import Mathlib
import Definitions.Def_FairKMeans_Model
import Definitions.Def_FairKMeans_RelaxedSolution

namespace FairKMeans

/-- **Lemma 17 (Mixing identity)**, p.22 (PDF 24). Cheng–Mo–Song–Ding, arXiv:2609.07974 (held
version, sha256 73e9312c…).

For `θ ∈ [0,1]` and relaxed solutions `φ₁, φ₂`, the θ-mixture `φ_θ = (1−θ)φ₁ ⊕ θφ₂` satisfies
`C_{T_θ} = (1−θ)C_{T₁} + θC_{T₂}` and `ν_p(φ_θ) = (1−θ)ν_p(φ₁) + θν_p(φ₂)` (24), and, with `L`
the linearized cost at `φ₁`,
`Ψ(φ_θ) = Ψ(φ₁) − θ(L(φ₁) − L(φ₂)) + λθ² ∑_p ‖ν_p(φ₁) − ν_p(φ₂)‖²` (25). -/
theorem lemma_17 {d n m s₁ s₂ : ℕ} (I : Instance d n m) (ρ : ℝ) (hρ : 1 ≤ ρ) (θ : ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (φ₁ : Fin n → Fin s₁ → ℝ) (φ₂ : Fin n → Fin s₂ → ℝ)
    (h₁ : IsRelaxed I φ₁) (h₂ : IsRelaxed I φ₂) :
    CT I (mixAssign θ φ₁ φ₂) = (1 - θ) * CT I φ₁ + θ * CT I φ₂ ∧
      (∀ p, nu I (mixAssign θ φ₁ φ₂) p = (1 - θ) • nu I φ₁ p + θ • nu I φ₂ p) ∧
      Psi I ρ (mixAssign θ φ₁ φ₂) =
        Psi I ρ φ₁ - θ * (linCost I ρ φ₁ φ₁ - linCost I ρ φ₁ φ₂)
          + lam ρ * θ ^ 2 * ∑ p, ‖nu I φ₁ p - nu I φ₂ p‖ ^ 2 := by sorry

end FairKMeans
