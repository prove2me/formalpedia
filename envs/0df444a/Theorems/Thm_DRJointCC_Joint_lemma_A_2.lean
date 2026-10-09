-- Prove2me | Theorems.Thm_DRJointCC_Joint_lemma_A_2
-- name    : DRJointCC.Joint.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:35:16.673988+00:00
-- url     : https://prove2.me/theorems/19b36c39-04fc-4184-8305-b23f3c681b91
-- title:
--   Lemma A.2, p. 31 — the worst-case probability of a Borel set is the value of an SDP over M ≽ 0 with [ξᵀ 1]M[ξᵀ 1]ᵀ ≥ 1 on S
-- statement:
--   Let $\mathcal P$ be the set of all probability distributions on $\mathbb R^k$ with mean $\mu$ and covariance $\Sigma\succ0$, and let $\Omega$ be the second-order moment matrix. For every Borel measurable set $\mathcal S\subseteq\mathbb R^k$ (not necessarily convex), the worst-case probability
--   $$
--   \pi_{\mathrm{wc}}=\sup_{\mathbb P\in\mathcal P}\mathbb P\{\tilde\xi\in\mathcal S\}
--   $$
--   satisfies
--   $$
--   \pi_{\mathrm{wc}}=\inf_{M\in\mathbb S^{k+1}}\Big\{\langle\Omega,M\rangle:\ M\succeq0,\ [\xi^\top\ 1]\,M\,[\xi^\top\ 1]^\top\ge1\ \ \forall\xi\in\mathcal S\Big\}.
--   $$
--
--   This generalized Chebyshev bound is what turns the strict robust joint chance constraint into a semidefinite constraint, with $\mathcal S$ the union of the closed half-spaces where some constraint is violated or active.
--
--   **Formalization Note** Both sides are extended reals (the left side is a probability, coerced). $M\succeq0$ is `Matrix.PosSemidef`, which includes symmetry. The statement is identical to the one drafted in the companion mission on individual chance constraints.
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, p. 31, Lemma A.2, (55)

import Mathlib
import Definitions.Def_DRJointCC_Joint_Joint

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Joint

/-- Lemma A.2, p. 31: the worst-case probability of a Borel set `S` over the moment set equals
the value of the SDP `inf { ⟨Ω, M⟩ : M ≽ 0, [ξᵀ 1] M [ξᵀ 1]ᵀ ≥ 1 ∀ ξ ∈ S }`. -/
theorem lemma_A_2 {k : ℕ} (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ) (hSig : Sig.PosDef)
    (S : Set (Fin k → ℝ)) (hS : MeasurableSet S) :
    ((⨆ P ∈ DRJointCC.Individual.ambiguitySet μ Sig, P S : ℝ≥0∞) : EReal) =
      ⨅ (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ)
        (_ : M.PosSemidef ∧ ∀ ξ ∈ S, 1 ≤ DRJointCC.Individual.liftQuad M ξ),
        ((DRJointCC.Individual.frob (DRJointCC.Individual.momentMatrix μ Sig) M : ℝ) : EReal) := by sorry

end DRJointCC.Joint
