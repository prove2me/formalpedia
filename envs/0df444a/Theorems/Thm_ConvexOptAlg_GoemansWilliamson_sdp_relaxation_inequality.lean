-- Prove2me | Theorems.Thm_ConvexOptAlg_GoemansWilliamson_sdp_relaxation_inequality
-- name    : ConvexOptAlg.GoemansWilliamson.sdp_relaxation_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T19:22:51.917071+00:00
-- url     : https://prove2.me/theorems/8999d78b-ef1c-4e11-ad59-d3a694dda45a
-- title:
--   §6.6, p. 345 — max over {−1,1}ⁿ of x⊤Lx = max ⟨L, xx⊤⟩ ≤ the value of the SDP relaxation
-- statement:
--   Let $A\in\mathbb R^{n\times n}$ and $L=D-A$ its Laplacian. Then
--
--   $$\max_{x\in\{-1,1\}^n}x^\top Lx=\max_{x\in\{-1,1\}^n}\langle L,xx^\top\rangle\le\max_{X\in\mathbb S^n_+,\ X_{i,i}=1,\ i\in[n]}\langle L,X\rangle.$$
--
--   Precisely: (1) the two maxima over the hypercube are equal; (2) for every $x\in\{-1,1\}^n$, the matrix $xx^\top$ is feasible for the relaxation (positive semidefinite with unit diagonal); (3) for every solution $\Sigma$ of the relaxation, $\max_{x\in\{-1,1\}^n}x^\top Lx\le\langle L,\Sigma\rangle$.
--
--   This is the inequality on which the Goemans–Williamson algorithm is based: the convex relaxation over-estimates the maximum cut.
--
--   **Formalization Note** The right-hand maximum is expressed through a solution $\Sigma$ of the relaxation (part 3), so no supremum over an infinite set is formed. The statement holds for every real matrix $A$; the book's hypotheses on $A$ (symmetric, non-negative) are not used and not assumed. Points of the hypercube are Boolean vectors read as $\pm1$ vectors.
-- source:
--   Bubeck, arXiv:1405.4980v2, §6.6, p. 345 (display before Theorem 6.11)

import Mathlib
import Definitions.Def_ConvexOptAlg_GoemansWilliamson_Defs

namespace ConvexOptAlg.GoemansWilliamson

open Matrix

/-- The relaxation inequality (Bubeck, arXiv:1405.4980v2, §6.6, p. 345):
`max_{x ∈ {−1,1}ⁿ} x⊤Lx = max_{x ∈ {−1,1}ⁿ} ⟨L, xx⊤⟩ ≤ max_{X ∈ S₊ⁿ, X i i = 1} ⟨L, X⟩`.

Stated as three facts about the Laplacian `L = D − A` of a real square matrix `A`: (1) the two
maxima over the hypercube coincide; (2) every `xx⊤` with `x ∈ {−1, 1}ⁿ` is feasible for the
relaxation; (3) the hypercube maximum is at most `⟨L, Σ⟩` for every solution `Σ` of the
relaxation. Points of the hypercube are encoded as Boolean vectors via `signOfBool`. -/
theorem sdp_relaxation_inequality {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    hypercubeMax (laplacian A) =
        Finset.univ.sup' Finset.univ_nonempty (fun b : Fin n → Bool =>
          frobInner (laplacian A)
            (vecMulVec (fun i => signOfBool (b i)) (fun i => signOfBool (b i)))) ∧
      (∀ b : Fin n → Bool,
        IsSDPFeasible (vecMulVec (fun i => signOfBool (b i)) (fun i => signOfBool (b i)))) ∧
      ∀ Sig : Matrix (Fin n) (Fin n) ℝ, IsSDPRelaxationOptimum (laplacian A) Sig →
        hypercubeMax (laplacian A) ≤ frobInner (laplacian A) Sig := by sorry

end ConvexOptAlg.GoemansWilliamson
