-- Prove2me | Theorems.Thm_DRJointCC_Joint_lemma_A_1
-- name    : DRJointCC.Joint.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:32:02.198387+00:00
-- url     : https://prove2.me/theorems/380c3457-65b9-4d58-a8b7-5ea060ebb309
-- title:
--   Lemma A.1, p. 30 — sup_P E_P[(f(ξ))⁺] equals inf ⟨Ω, M⟩ over M ≽ 0 with [ξᵀ 1]M[ξᵀ 1]ᵀ ≥ f(ξ) for all ξ
-- statement:
--   Let $\mathcal P$ be the set of all probability distributions on $\mathbb R^k$ with mean $\mu$ and covariance $\Sigma\succ0$, and let $\Omega$ be the second-order moment matrix. For every measurable function $f:\mathbb R^k\to\mathbb R$, the worst-case expectation
--   $$
--   \theta_{\mathrm{wc}}=\sup_{\mathbb P\in\mathcal P}\mathbb E_{\mathbb P}\big((f(\tilde\xi))^+\big)
--   $$
--   satisfies
--   $$
--   \theta_{\mathrm{wc}}=\inf_{M\in\mathbb S^{k+1}}\Big\{\langle\Omega,M\rangle:\ M\succeq0,\ [\xi^\top\ 1]\,M\,[\xi^\top\ 1]^\top\ge f(\xi)\ \ \forall\xi\in\mathbb R^k\Big\}.
--   $$
--
--   This is the strong duality of the moment problem for the positive part of a function; it turns the worst-case expectations appearing in a worst-case CVaR into semidefinite programs.
--
--   **Formalization Note** Both sides are extended reals: the left side may be $+\infty$, and the infimum over an empty feasible set is $+\infty$. $M\succeq0$ is `Matrix.PosSemidef`, which includes symmetry, so $M$ ranges over $\mathbb S^{k+1}$. The statement is identical to the one drafted in the companion mission on individual chance constraints.
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, p. 30, Lemma A.1

import Mathlib
import Definitions.Def_DRJointCC_Joint_Joint

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Joint

/-- Lemma A.1, p. 30: the worst-case expectation `sup_{ℙ ∈ 𝒫} E_ℙ((f(ξ̃))⁺)` of a measurable
`f` equals the value of the SDP `inf { ⟨Ω, M⟩ : M ≽ 0, [ξᵀ 1] M [ξᵀ 1]ᵀ ≥ f(ξ) ∀ ξ }`
(both sides may be `+∞`). -/
theorem lemma_A_1 {k : ℕ} (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ) (hSig : Sig.PosDef)
    (f : (Fin k → ℝ) → ℝ) (hf : Measurable f) :
    DRJointCC.Individual.wcExpPos μ Sig f =
      ⨅ (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ)
        (_ : M.PosSemidef ∧ ∀ ξ, f ξ ≤ DRJointCC.Individual.liftQuad M ξ),
        ((DRJointCC.Individual.frob (DRJointCC.Individual.momentMatrix μ Sig) M : ℝ) : EReal) := by sorry

end DRJointCC.Joint
