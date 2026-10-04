-- Prove2me | Theorems.Thm_AronszajnRK_Sum_disjoint_sum
-- name    : AronszajnRK.Sum.disjoint_sum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T04:49:13.729331+00:00
-- url     : https://prove2.me/theorems/018a1279-95e0-4597-af5d-ea5795f30af3
-- title:
--   §6, p. 354 — the disjoint case: ‖f‖² = ‖f₁‖₁² + ‖f₂‖₂², and F₁, F₂ complementary closed subspaces
-- statement:
--   Let $F_1$, $F_2$ be complex Hilbert spaces of functions on a set $E$ with reproducing kernels $K_1$, $K_2$ and norms $\|\cdot\|_1$, $\|\cdot\|_2$, and let $F$ be a complex Hilbert space of functions on $E$ with reproducing kernel $K_1+K_2$. Suppose first that $F_1$ and $F_2$ **have no function besides zero in common**. Then for every $f\in F$ and every decomposition $f=f_1+f_2$ with $f_i\in F_i$,
--   $$\|f\|^2=\|f_1\|_1^2+\|f_2\|_2^2 .$$
--   Moreover, $F_1$ and $F_2$ have no function besides zero in common **if and only if** $F_1$ and $F_2$ are complementary closed subspaces of $F$: there is a closed subspace $S_1$ of $F$ with orthogonal complement $S_2$ such that $S_1$ consists exactly of the functions of $F_1$, $S_2$ exactly of the functions of $F_2$, and each function of $F_i$ has the same norm in $F$ as in $F_i$.
--
--   This is the case in which the sum of kernels corresponds to an orthogonal direct sum of spaces.
--
--   **Formalization Note** "Subspace" is the paper's notion of §1: a subclass on which the two norms agree. "No function besides zero in common" is equality of the intersection of the two sets of functions with $\{0\}$.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 354, §6 (unnumbered, after the Theorem)

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn

namespace AronszajnRK.Sum

/-- **The disjoint case of the sum** (Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer.
Math. Soc. 68 (1950), §6, p. 354 (PDF 18)): when the classes `F₁` and `F₂` have no function besides
zero in common, the norm in `F` (the class with kernel `K₁ + K₂`) is given simply by
`‖f‖² = ‖f₁‖₁² + ‖f₂‖₂²`. In this case (and only in this case) `F₁` and `F₂` are complementary
closed subspaces of `F`.

"Subspace" is the paper's notion (§1, p. 343): a subclass on which the two norms agree. Here
`F₁` is a closed subspace of `F` with complement `F₂` when there are closed `S₁`, `S₂ = S₁ᗮ` in
`H` whose elements are exactly the functions of `F₁`, respectively `F₂`, each with the norm it has
in `H₁`, respectively `H₂`. -/
theorem disjoint_sum {X : Type*}
    {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [RKHS ℂ H₁ X ℂ]
    {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    [RKHS ℂ H₂ X ℂ]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [RKHS ℂ H X ℂ] (hK : kernelFn H = kernelFn H₁ + kernelFn H₂) :
    (Set.range (fun f : H₁ => (f : X → ℂ)) ∩ Set.range (fun f : H₂ => (f : X → ℂ)) = {0} →
      ∀ (f : H) (f₁ : H₁) (f₂ : H₂), (f : X → ℂ) = (f₁ : X → ℂ) + (f₂ : X → ℂ) →
        ‖f‖ ^ 2 = ‖f₁‖ ^ 2 + ‖f₂‖ ^ 2) ∧
    (Set.range (fun f : H₁ => (f : X → ℂ)) ∩ Set.range (fun f : H₂ => (f : X → ℂ)) = {0} ↔
      ∃ S₁ S₂ : Submodule ℂ H, IsClosed (S₁ : Set H) ∧ S₂ = S₁ᗮ ∧
        (∀ f₁ : H₁, ∃ f ∈ S₁, (f : X → ℂ) = (f₁ : X → ℂ) ∧ ‖f‖ = ‖f₁‖) ∧
        (∀ f ∈ S₁, ∃ f₁ : H₁, (f : X → ℂ) = (f₁ : X → ℂ)) ∧
        (∀ f₂ : H₂, ∃ f ∈ S₂, (f : X → ℂ) = (f₂ : X → ℂ) ∧ ‖f‖ = ‖f₂‖) ∧
        (∀ f ∈ S₂, ∃ f₂ : H₂, (f : X → ℂ) = (f₂ : X → ℂ))) := by sorry

end AronszajnRK.Sum
