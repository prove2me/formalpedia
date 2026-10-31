-- Prove2me | Theorems.Thm_AubinLipschitz_clarkeDeriv_paramMap_surjective_iff
-- name    : AubinLipschitz.clarkeDeriv_paramMap_surjective_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:52:50.443821+00:00
-- url     : https://prove2.me/theorems/50ef2c6e-0c84-4e36-abd5-22dfff96a5d4
-- title:
--   §5, Corollary 1 — surjectivity of $CF$ is surjectivity of the matrix
-- statement:
--   In the setting of Lemma 1 of §5, the closed convex process $CF(x_0,q_0;p_0,y_0,A_0)$, from $X\times Y^*$ to $X^*\times Y\times L(X,Y)$, is surjective if and only if the closed convex process
--
--   $$
--   \begin{pmatrix}CG(x_0,p_0-A_0^*q_0) & A_0^*\\[2pt] -A_0 & \big(CH(A_0x_0+y_0,q_0)\big)^{-1}\end{pmatrix},
--   $$
--
--   from $X\times Y^*$ to $X^*\times Y$, is surjective.
--
--   This reduces the hypothesis of the Inverse Function Theorem to the condition in the goal.
--
--   Differences from the source:
--   - generalization: G = ∂U and H = ∂V → arbitrary set-valued G from X to X* and H from Y to Y*; reason: the argument uses Lemma 1 and (2.18) only, and the choice G = ∂U, H = ∂V gives the paper's statement.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §5, Corollary 1, pp.34–35

import Mathlib
import Definitions.Def_AubinLipschitz_blockProcess
import Definitions.Def_AubinLipschitz_clarkeDeriv
import Definitions.Def_AubinLipschitz_invMap
import Definitions.Def_AubinLipschitz_IsSurjectiveProcess
import Definitions.Def_AubinLipschitz_paramMap

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §5, Corollary 1, pp.34–35: in the setting of Lemma 1, the closed convex process
`CF(x₀, q₀; p₀, y₀, A₀)` is surjective if and only if the closed convex process
`[[CG(x₀, p₀ − A₀*q₀), A₀*], [−A₀, (CH(A₀x₀ + y₀, q₀))⁻¹]]` is surjective. -/
theorem clarkeDeriv_paramMap_surjective_iff {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (G : X → Set (StrongDual ℝ X)) (H : Y → Set (StrongDual ℝ Y)) (A₀ : X →L[ℝ] Y)
    (p₀ : StrongDual ℝ X) (y₀ : Y) (x₀ : X) (q₀ : StrongDual ℝ Y)
    (h₁ : ∃ g ∈ G x₀, p₀ = g + q₀.comp A₀) (h₂ : ∃ h ∈ invMap H q₀, y₀ = -(A₀ x₀) + h) :
    IsSurjectiveProcess (clarkeDeriv (paramMap G (invMap H)) (x₀, q₀) (p₀, y₀, A₀)) ↔
      IsSurjectiveProcess
        (blockProcess (clarkeDeriv G x₀ (p₀ - q₀.comp A₀)) A₀
          (invMap (clarkeDeriv H (A₀ x₀ + y₀) q₀))) := by sorry

end AubinLipschitz
