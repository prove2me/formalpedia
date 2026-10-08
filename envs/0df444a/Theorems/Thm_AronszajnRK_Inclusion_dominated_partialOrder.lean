-- Prove2me | Theorems.Thm_AronszajnRK_Inclusion_dominated_partialOrder
-- name    : AronszajnRK.Inclusion.dominated_partialOrder
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:29:06.154316+00:00
-- url     : https://prove2.me/theorems/e7e0ef0a-4cf6-429e-a9d6-6fa85c74f108
-- title:
--   §7, p. 354 — $\ll$ is a partial order on positive matrices
-- statement:
--   Let $K_1, K_2, K_3 : X\times X\to\mathbb C$ be positive matrices on a set $X$. Then
--
--   1. if $K_1\ll K_2$ and $K_2\ll K_3$, then $K_1\ll K_3$;
--   2. if $K_1\ll K_2$ and $K_2\ll K_1$, then $K_1 = K_2$ (as functions on $X\times X$).
--
--   $$K_1\ll K_2\ll K_3 \implies K_1\ll K_3, \qquad K_1\ll K_2,\ K_2\ll K_1 \implies K_1=K_2 .$$
--
--   Together with reflexivity, which is immediate, this shows that $\ll$ is a partial ordering of the class of positive matrices; the inclusion theorems for reproducing kernel classes are statements about this order.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 354, §7 (unnumbered remark after (1))

import Mathlib
import Definitions.Def_AronszajnRK_Limits_KernelLE

open scoped ComplexOrder

namespace AronszajnRK.Inclusion

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §7, p. 354
(PDF p. 18), unnumbered: on positive matrices, `≪` is a partial ordering. From
`K₁ ≪ K₂ ≪ K₃` it follows that `K₁ ≪ K₃`; if `K₁ ≪ K₂` and `K₂ ≪ K₁`, then `K₁ = K₂`. -/
theorem dominated_partialOrder {X : Type*} (K₁ K₂ K₃ : X → X → ℂ)
    (h₁ : (Matrix.of K₁).PosSemidef) (h₂ : (Matrix.of K₂).PosSemidef)
    (h₃ : (Matrix.of K₃).PosSemidef) :
    (AronszajnRK.Limits.KernelLE K₁ K₂ → AronszajnRK.Limits.KernelLE K₂ K₃ → AronszajnRK.Limits.KernelLE K₁ K₃) ∧
      (AronszajnRK.Limits.KernelLE K₁ K₂ → AronszajnRK.Limits.KernelLE K₂ K₁ → K₁ = K₂) := by sorry

end AronszajnRK.Inclusion
