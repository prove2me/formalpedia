-- Prove2me | Theorems.Thm_AdaptiveSparsify_lemma_4_10
-- name    : AdaptiveSparsify.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:43:57.114343+00:00
-- url     : https://prove2.me/theorems/b0258f8a-388b-4373-bf0d-9ba4a2970c5c
-- title:
--   Lemma 4.10 — second-order bound on the change of one block of the potential
-- statement:
--   Let $\Psi(\mu)=\exp(\lambda\|\mu\|^2_{M_\mu})$, $\mu^{\mathrm{new}}=\mu-\delta_\mu$ with $\|\delta_\mu\|_{M_\mu}\le\varepsilon^2$, and $M_{\mu^{\mathrm{new}}}\approx_{\varepsilon^2}M_\mu$. Then there is an absolute constant $C$ with
--
--   $$\Psi(\mu^{\mathrm{new}})\le\Psi(\mu)-2e^{\lambda\|\mu\|^2_{M_\mu}}\lambda\,\delta_\mu^\top M_\mu\mu+Ce^{\lambda\|\mu\|^2_{M_\mu}}\,e^{C\lambda[\|\mu\|_{M_\mu}\|\delta_\mu\|_{M_\mu}+\|\delta_\mu\|^2_{M_\mu}+\varepsilon^2\|\mu\|^2_{M_\mu}]}\,\lambda\big[\varepsilon^2\|\mu\|^2_{M_\mu}+(1+\lambda\|\mu\|^2_{M_\mu})\|\delta_\mu\|^2_{M_\mu}\big].$$
--
--   Here $M_\mu$ and $M_{\mu^{\mathrm{new}}}$ are positive definite, $0<\varepsilon<1/80$ and $\lambda>0$. This single-block estimate drives both the centrality potential of Lemma 4.7 and the stability potential of Lemma 4.15.
--
--   Differences from the source:
--   - reading: ε and λ unrestricted in the lemma → 0 < ε < 1/80 (p.17) and λ > 0; reason: the standing range of §4
--   - generalization: M_µ and M_{µ^new} the matrices attached to µ and µ^new → any two positive definite matrices of the same size, related by ≈_{ε²}, also when δ_µ = 0 and M_{µ^new} ≠ M_µ; reason: the lemma uses no other property of them; every instance of the page is an instance here
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), Lemma 4.10, p.20

import Mathlib
import Definitions.Def_AdaptiveSparsify_Linear

open Matrix

namespace AdaptiveSparsify

/-- **Lemma 4.10**, p.20.

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…), Lemma 4.10, p.20.

"Let Ψ(µ) = exp(λ‖µ‖²_{M_µ}), µ^new = µ − δ_µ for ‖δ_µ‖_{M_µ} ≤ ε², and M_{µ^new} ≈_{ε²} M_µ. Then, for an
absolute constant C, Ψ(µ^new) ≤ Ψ(µ) − 2 exp(λ‖µ‖²_{M_µ}) λ δ_µ⊤ M_µ µ + C exp(λ‖µ‖²_{M_µ}) exp(Cλ[‖µ‖_{M_µ}‖δ_µ‖_{M_µ} +
‖δ_µ‖²_{M_µ} + ε²‖µ‖²_{M_µ}]) · λ[ε²‖µ‖²_{M_µ} + (1 + λ‖µ‖²_{M_µ})‖δ_µ‖²_{M_µ}]."

**Formalization Note.** `M_µ` and `M_{µ^new}` are any positive definite matrices of the same size, `ε` is
§4's constant (`ε < 1/80`, p.17), and `λ > 0`. The constant `C` is chosen before all of them. -/
theorem lemma_4_10 : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (M Mnew : Matrix (Fin N) (Fin N) ℝ)
    (μ δ : Fin N → ℝ) (ε lam : ℝ),
    0 < ε → ε < 1 / 80 → 0 < lam → M.PosDef → Mnew.PosDef →
    wNorm M δ ≤ ε ^ 2 → ApproxEq (ε ^ 2) Mnew M →
    Real.exp (lam * quadForm Mnew (μ - δ)) ≤
      Real.exp (lam * quadForm M μ) -
        2 * Real.exp (lam * quadForm M μ) * lam * (δ ⬝ᵥ (M *ᵥ μ)) +
        C * Real.exp (lam * quadForm M μ) *
          Real.exp (C * lam *
            (wNorm M μ * wNorm M δ + quadForm M δ + ε ^ 2 * quadForm M μ)) *
          (lam * (ε ^ 2 * quadForm M μ + (1 + lam * quadForm M μ) * quadForm M δ)) := by sorry

end AdaptiveSparsify
