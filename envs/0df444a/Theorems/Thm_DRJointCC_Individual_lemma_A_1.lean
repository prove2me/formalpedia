-- Prove2me | Theorems.Thm_DRJointCC_Individual_lemma_A_1
-- name    : DRJointCC.Individual.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:36:29.443755+00:00
-- url     : https://prove2.me/theorems/29ca4055-9261-4945-a7c7-7736981dbf85
-- title:
--   Lemma A.1, p. 30 — the worst-case expectation of f⁺ is the value of an SDP
-- statement:
--   Let $\mathcal P$ be the set of all probability distributions on $\mathbb R^k$ with mean $\mu$ and covariance matrix $\Sigma\succ0$, and let $\Omega$ be the second-order moment matrix. Let $f:\mathbb R^k\to\mathbb R$ be a measurable function and define the worst-case expectation $\theta_{\mathrm{wc}}=\sup_{\mathbb P\in\mathcal P}\mathbb E_{\mathbb P}\big((f(\tilde\xi))^+\big)$. Then
--
--   $$
--   \theta_{\mathrm{wc}}=\inf_{M\in\mathbb S^{k+1}}\Big\{\langle\Omega,M\rangle:\ M\succeq0,\ [\xi^\top\ 1]\,M\,[\xi^\top\ 1]^\top\ge f(\xi)\ \ \forall\xi\in\mathbb R^k\Big\}.
--   $$
--
--   This is a strong duality theorem for a moment problem. It turns the inner supremum of the worst-case CVaR into a semidefinite program.
--
--   **Formalization Note** Both sides are extended reals and may equal $+\infty$, for instance when $f$ grows faster than quadratically; then no $M$ is feasible and the infimum is $+\infty$. The expectation of the positive part is a lower Lebesgue integral.
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, p. 30, Lemma A.1

import Mathlib
import Definitions.Def_DRJointCC_Individual_Individual

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Individual

/-- Lemma A.1, p. 30: the worst-case expectation `sup_{ℙ ∈ 𝒫} E_ℙ((f(ξ̃))⁺)` of a measurable
`f` equals the value of the SDP `inf { ⟨Ω, M⟩ : M ≽ 0, [ξᵀ 1] M [ξᵀ 1]ᵀ ≥ f(ξ) ∀ ξ }`
(both sides may be `+∞`). -/
theorem lemma_A_1 {k : ℕ} (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ) (hSig : Sig.PosDef)
    (f : (Fin k → ℝ) → ℝ) (hf : Measurable f) :
    wcExpPos μ Sig f =
      ⨅ (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ)
        (_ : M.PosSemidef ∧ ∀ ξ, f ξ ≤ liftQuad M ξ),
        ((frob (momentMatrix μ Sig) M : ℝ) : EReal) := by sorry

end DRJointCC.Individual
