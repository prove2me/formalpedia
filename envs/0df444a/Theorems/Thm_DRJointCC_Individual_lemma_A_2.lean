-- Prove2me | Theorems.Thm_DRJointCC_Individual_lemma_A_2
-- name    : DRJointCC.Individual.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:36:41.110927+00:00
-- url     : https://prove2.me/theorems/5550e4f3-b253-430c-b617-e0dbce45ead8
-- title:
--   Lemma A.2, p. 31 — the worst-case probability of a Borel set is the value of an SDP
-- statement:
--   Let $\mathcal P$ be the set of probability distributions on $\mathbb R^k$ with mean $\mu$ and covariance $\Sigma\succ0$, and let $\Omega$ be the second-order moment matrix. Let $\mathcal S\subseteq\mathbb R^k$ be any Borel measurable set, not necessarily convex, and define the worst-case probability $\pi_{\mathrm{wc}}=\sup_{\mathbb P\in\mathcal P}\mathbb P\{\tilde\xi\in\mathcal S\}$. Then
--
--   $$
--   \pi_{\mathrm{wc}}=\inf_{M\in\mathbb S^{k+1}}\Big\{\langle\Omega,M\rangle:\ M\succeq0,\ [\xi^\top\ 1]\,M\,[\xi^\top\ 1]^\top\ge1\ \ \forall\xi\in\mathcal S\Big\}.
--   $$
--
--   This is a strong duality theorem for a moment problem (a generalized Chebyshev inequality). The proof of Theorem 2.2 applies it to the set $\mathcal S=\{\xi:L(\xi)>\gamma\}$.
--
--   **Formalization Note** The left side is a supremum in $[0,\infty]$, coerced to the extended reals; the right side is an infimum in the extended reals, equal to $+\infty$ if no $M$ is feasible. $M\succeq0$ is `Matrix.PosSemidef`.
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, p. 31, Lemma A.2

import Mathlib
import Definitions.Def_DRJointCC_Individual_Individual

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Individual

/-- Lemma A.2, p. 31: the worst-case probability of a Borel set `S` over the moment set equals
the value of the SDP `inf { ⟨Ω, M⟩ : M ≽ 0, [ξᵀ 1] M [ξᵀ 1]ᵀ ≥ 1 ∀ ξ ∈ S }`. -/
theorem lemma_A_2 {k : ℕ} (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ) (hSig : Sig.PosDef)
    (S : Set (Fin k → ℝ)) (hS : MeasurableSet S) :
    ((⨆ P ∈ ambiguitySet μ Sig, P S : ℝ≥0∞) : EReal) =
      ⨅ (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ)
        (_ : M.PosSemidef ∧ ∀ ξ ∈ S, 1 ≤ liftQuad M ξ),
        ((frob (momentMatrix μ Sig) M : ℝ) : EReal) := by sorry

end DRJointCC.Individual
