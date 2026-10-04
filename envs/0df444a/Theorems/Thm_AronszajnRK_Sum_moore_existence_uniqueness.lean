-- Prove2me | Theorems.Thm_AronszajnRK_Sum_moore_existence_uniqueness
-- name    : AronszajnRK.Sum.moore_existence_uniqueness
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T04:48:28.954551+00:00
-- url     : https://prove2.me/theorems/8661ee4a-7bdb-4b7e-a11c-e9ccc2f06fa0
-- title:
--   §2 (4) — Moore's theorem: a positive matrix is the kernel of one and only one Hilbert space of functions
-- statement:
--   Let $E$ be a set and $K:E\times E\to\mathbb C$ a **positive matrix** in the sense of E. H. Moore: for every $n$, all points $y_1,\dots,y_n\in E$ and all $\xi_1,\dots,\xi_n\in\mathbb C$,
--   $$\sum_{i,j=1}^n K(y_i,y_j)\,\bar\xi_i\,\xi_j\ \ge 0 .$$
--   Then:
--
--   1. (*existence*) there is a complex Hilbert space of functions on $E$ with continuous point evaluations whose reproducing kernel is $K$;
--   2. (*uniqueness*) if $F_1$ and $F_2$ are two such spaces with reproducing kernel $K$, they consist of the same functions, and every function has the same norm in $F_1$ as in $F_2$.
--
--   Hence $K$ determines its class of functions together with its quadratic form $\|f\|^2$. This is what makes "the class with kernel $K$" a well-defined object, which every other statement of the mission uses.
--
--   **Formalization Note** A positive matrix is `(Matrix.of K).PosSemidef` (Hermitian with non-negative finitely supported quadratic form $\sum\bar\xi_i K(y_i,y_j)\xi_j$, no finiteness of $E$). The two spaces in the uniqueness half are quantified over arbitrary universes; the existence witness lives in the universe of $E$. Equality of norms gives equality of scalar products by polarization. Existence alone is Mathlib's `RKHS.OfKernel` construction (after converting the scalar kernel to an operator-valued one); uniqueness is not in Mathlib.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 344, §2 (4)

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn

open scoped ComplexOrder

namespace AronszajnRK.Sum

universe u v w

/-- **Moore's theorem** (Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68
(1950), §2 (4), p. 344 (PDF 8)): to every positive matrix `K(x, y)` there corresponds one and only
one class of functions with a uniquely determined quadratic form in it, forming a Hilbert space and
admitting `K(x, y)` as a reproducing kernel.

A positive matrix (§2 (3), p. 344) is `(Matrix.of K).PosSemidef`: `K` is Hermitian and
`∑ᵢⱼ K(yᵢ, yⱼ) ξ̄ᵢ ξⱼ ≥ 0` for every finite family. Existence: some complex RKHS on `X` has scalar
kernel `K`. Uniqueness: any two complex RKHSs on `X` with scalar kernel `K` contain the same
functions, and an element of either has the same norm (quadratic form) as the element of the other
with the same function. -/
theorem moore_existence_uniqueness {X : Type u} (K : X → X → ℂ)
    (hK : (Matrix.of K).PosSemidef) :
    (∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
        (_ : RKHS ℂ H X ℂ), kernelFn H = K) ∧
    ∀ (H₁ : Type v) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
      [RKHS ℂ H₁ X ℂ] (H₂ : Type w) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
      [CompleteSpace H₂] [RKHS ℂ H₂ X ℂ],
      kernelFn H₁ = K → kernelFn H₂ = K →
        Set.range (fun f : H₁ => (f : X → ℂ)) = Set.range (fun f : H₂ => (f : X → ℂ)) ∧
        ∀ (f₁ : H₁) (f₂ : H₂), (f₁ : X → ℂ) = (f₂ : X → ℂ) → ‖f₁‖ = ‖f₂‖ := by sorry

end AronszajnRK.Sum
