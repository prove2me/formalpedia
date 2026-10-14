-- Prove2me | Theorems.Thm_CauchyRiemannIndex_asymptoticCZIndex_conj
-- name    : CauchyRiemannIndex.asymptoticCZIndex_conj
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-13T21:03:53.935972+00:00
-- url     : https://prove2.me/theorems/afb23524-057d-4fd5-8ce6-7ca13bdc9ed4
-- title:
--   The Conley–Zehnder index of the conjugate asymptotic operator
-- statement:
--   Let $S$ be a continuous loop of symmetric matrices whose asymptotic operator $A=-J_0\partial_t-S$ is nondegenerate, and let $C$ be complex conjugation on $\mathbb{C}^n=\mathbb{R}^{2n}$. Then the conjugate asymptotic operator $\bar A=-J_0\partial_t+CSC$ is nondegenerate and
--   $$\mu_{CZ}(\bar A)=-\mu_{CZ}(A).$$
--
--   **Formalization Note** $C$ is `conjMat n` and $\bar A$ is the asymptotic operator of the loop `fun t => -(conjMat n * S t * conjMat n)`. In Wendl, $\bar A=-A$ acts on the conjugate bundle and the index is taken in the conjugate trivialization; written in the original coordinates this is the operator above.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 5, Lemma 5.8, p. 87 (Conley–Zehnder part, trivial bundle)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Wendl, Lemma 5.8 (p. 87), Conley–Zehnder part, trivial bundle: for a nondegenerate loop `S` of
symmetric matrices, the conjugate asymptotic operator `-J₀ ∂ₜ - S̄`, `S̄ = -C S C` with `C`
complex conjugation, is nondegenerate and `μ_CZ(-J₀ ∂ₜ - S̄) = -μ_CZ(-J₀ ∂ₜ - S)`. -/
theorem asymptoticCZIndex_conj (n : ℕ) (S : ℝ → Mat n) (hS : IsSymLoop S)
    (hn : IsNondegenerate S) :
    IsNondegenerate (fun t => -(conjMat n * S t * conjMat n)) ∧
      asymptoticCZIndex (fun t => -(conjMat n * S t * conjMat n)) = -asymptoticCZIndex S := by
  sorry

end CauchyRiemannIndex
