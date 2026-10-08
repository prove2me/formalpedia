-- Prove2me | Theorems.Thm_AronszajnRK_Operators_opKernel_comp
-- name    : AronszajnRK.Operators.opKernel_comp
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:12:55.495976+00:00
-- url     : https://prove2.me/theorems/4e38f038-a799-4d69-aa49-f274dc19efc1
-- title:
--   §11, (4) — the kernel of a composition $L_1 L_2$
-- statement:
--   Let $F$ be a complex Hilbert space of functions on a set $E$ with reproducing kernel $K$, and let $L_1, L_2$ be bounded operators on $F$ with kernels $\Lambda_1, \Lambda_2$. For all $y, z \in E$, the functions $x \mapsto \Lambda_1(x, z)$ and $x \mapsto \overline{\Lambda_2(y, x)}$ belong to $F$, and the kernel $\Lambda$ of the composition $L = L_1 L_2$ (first $L_2$, then $L_1$) is their scalar product in the variable $x$:
--   $$
--   \Lambda(y, z) = \big(\Lambda_1(x, z),\ \overline{\Lambda_2(y, x)}\big)_x .
--   $$
--
--   This is the kernel analogue of matrix multiplication; the second factor is the kernel of $L_2^*$ by the adjoint formula (3).
--
--   **Formalization Note.** The statement asserts the existence of elements `g₁ g₂ : H` with `⇑g₁ = fun x => Λ₁(x, z)` and `⇑g₂ = fun x => conj (Λ₂(y, x))` (such elements are unique, since `H` injects into functions) and `Λ(y, z) = ⟪g₂, g₁⟫_ℂ`: the paper's $(g_1, g_2)$ is Mathlib's `⟪g₂, g₁⟫_ℂ`. On the one-point space with $K = 1$, $L_1 = a I$, $L_2 = b I$ both sides equal $\overline{ab}$.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 372, §11, Eq. (4)

import Mathlib
import Definitions.Def_AronszajnRK_Operators_opKernel

open scoped InnerProductSpace
open ComplexConjugate

namespace AronszajnRK.Operators

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §11, Eq. (4),
p. 372 (PDF p. 36): the kernel `Λ` of the composition `L = L₁L₂` is
`Λ(y, z) = (Λ₁(x, z), \overline{Λ₂(y, x)})ₓ`, the scalar product in `x` of two elements of the
space: the function `x ↦ Λ₁(x, z)` and the function `x ↦ \overline{Λ₂(y, x)}` both belong to
the space, and Aronszajn's scalar product `(g₁, g₂)` (linear in `g₁`) is Mathlib's
`⟪g₂, g₁⟫_ℂ`. -/
theorem opKernel_comp {H : Type*} {X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H X ℂ] (L₁ L₂ : H →L[ℂ] H) (y z : X) :
    ∃ g₁ g₂ : H, ⇑g₁ = (fun x => opKernel L₁ x z) ∧ ⇑g₂ = (fun x => conj (opKernel L₂ y x)) ∧
      opKernel (L₁ ∘L L₂) y z = ⟪g₂, g₁⟫_ℂ := by sorry

end AronszajnRK.Operators
