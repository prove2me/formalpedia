-- Prove2me | Theorems.Thm_DRSub4633_lemma_3_2_ii
-- name    : DRSub4633.lemma_3_2_ii
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T23:57:40.735689+00:00
-- url     : https://prove2.me/theorems/fef5edd2-cb01-49f3-9fcd-6ebb0476a9b5
-- title:
--   Lemma 3.2(ii) — affine reparametrization with a nonnegative matrix
-- statement:
--   Let $f:[0,1]^d\to\mathbb R$ be continuously differentiable and DR-submodular, let $M\in\mathbb R^{d\times d'}$ be entrywise nonnegative and let $c\in\mathbb R^d$ satisfy $c+Mz\in[0,1]^d$ for every $z\in[0,1]^{d'}$. Then
--   $$z\mapsto f(c+Mz)$$
--   is continuously differentiable and DR-submodular on $[0,1]^{d'}$, and it is nonnegative on $[0,1]^{d'}$ if $f$ is nonnegative on $[0,1]^d$.
--
--   The lemma is how DR-submodularity passes to slices and affine images such as $F(a(t),\cdot)$ and $Q_t$.
--
--   Differences from the source:
--   - encoding: objective defined on Q only; R^n with coordinatewise order; C^1 with boundary derivatives the continuous extensions of interior ones → f a total function on EuclideanSpace ℝ (Fin n), hypotheses on the cube only, values off the cube never read; the order written coordinatewise; GeomDRSub.IsDRSubmodular (ContDiffOn ℝ 1 on the cube, fderivWithin the cube); reason: Lean convention; on the cube the within-cube derivative of a C^1 function is the continuous extension of the interior derivative, so the instances are the same
--   - encoding: Mz → Matrix.toEuclideanLin M z; reason: Lean convention; same map
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Lemma 3.2(ii), p.8

import Mathlib
import Definitions.Def_GeomDRSub_IsDRSubmodular

namespace DRSub4633

/-- **Lemma 3.2(ii) (Consequences of DR-submodularity).** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Lemma 3.2(ii), p.8: "If
`M ∈ ℝ^(d×d′)` is entrywise nonnegative and `c + Mz ∈ [0, 1]^d` for every `z ∈ [0, 1]^d′`, then
`z ↦ f(c + Mz)` is `C¹` and DR-submodular on `[0, 1]^d′`, and it is nonnegative if `f` is."
(Standing hypothesis of Lemma 3.2: `f : [0, 1]^d → ℝ` is `C¹` and DR-submodular.)

**Formalization Note.** `Mz` is `Matrix.toEuclideanLin M z`. `C¹` and DR-submodular on
`[0, 1]^d′` is `GeomDRSub.IsDRSubmodular` on `ℝ^d′`. Every `d, d′` is allowed. -/
theorem lemma_3_2_ii {d d' : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : GeomDRSub.IsDRSubmodular f) (M : Matrix (Fin d) (Fin d') ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (hM : ∀ i j, 0 ≤ M i j)
    (hc : ∀ z ∈ GeomDRSub.cube d', c + Matrix.toEuclideanLin M z ∈ GeomDRSub.cube d) :
    GeomDRSub.IsDRSubmodular (fun z : EuclideanSpace ℝ (Fin d') => f (c + Matrix.toEuclideanLin M z)) ∧
    ((∀ y ∈ GeomDRSub.cube d, 0 ≤ f y) →
      ∀ z ∈ GeomDRSub.cube d', 0 ≤ f (c + Matrix.toEuclideanLin M z)) := by sorry

end DRSub4633
