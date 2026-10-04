-- Prove2me | Theorems.Thm_AronszajnRK_Sum_closed_subspace_kernels
-- name    : AronszajnRK.Sum.closed_subspace_kernels
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T04:49:30.866471+00:00
-- url     : https://prove2.me/theorems/790f9342-6d4c-4dba-ba80-57a5e41e0835
-- title:
--   §2 (7) — closed subspaces have reproducing kernels, and K′ + K″ = K for complementary subspaces
-- statement:
--   Let $F$ be a complex Hilbert space of functions on a set $E$ with reproducing kernel $K$, and let $F'\subseteq F$ be a closed linear subspace with orthogonal complement $F''=F'^{\perp}$. Then
--
--   1. $F'$ possesses a reproducing kernel, i.e. there are $k'_y\in F'$ ($y\in E$) with $f(y)=(f,k'_y)$ for all $f\in F'$;
--   2. whenever $k'$ is a reproducing kernel of $F'$ and $k''$ a reproducing kernel of $F''$, the scalar kernels $K'(x,y)=k'_y(x)$ and $K''(x,y)=k''_y(x)$ satisfy
--   $$K'(x,y)+K''(x,y)=K(x,y)\qquad\text{for all }x,y\in E.$$
--
--   Since every closed subspace is covered by part 1, $F''$ also has a reproducing kernel. The identity decomposes a kernel along an orthogonal decomposition of its space; it is the special case of the sum theorem of §6 in which the two summand classes are orthogonal.
--
--   **Formalization Note** "Complementary subspaces" is read as a closed subspace and its orthogonal complement. The kernels of $F'$ and $F''$ are any families with the reproducing property on those subspaces (definition `IsReproducingKernelOn`); they are not defined as projections of $K$, which would make the identity a restatement of §2 (6).
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 345, §2 (7)

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn
import Definitions.Def_AronszajnRK_Sum_IsReproducingKernelOn

namespace AronszajnRK.Sum

/-- (Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §2 (7),
p. 345 (PDF 9).) If `F` possesses a r.k. `K`, then the same is true of all closed linear subspaces
of `F`; if `F′` and `F″` are complementary subspaces of `F`, then their reproducing kernels satisfy
`K′ + K″ = K`.

Reading decision: "complementary subspaces" is read as a closed subspace `F′` and its orthogonal
complement `F″ = F′ᗮ`. The reproducing kernels of `F′` and `F″` are any `k′`, `k″` with the
reproducing property on that subspace (`IsReproducingKernelOn`), not the projections of `K`. -/
theorem closed_subspace_kernels {X : Type*} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]
    (F' : Submodule ℂ H) (hF' : IsClosed (F' : Set H)) :
    (∃ k' : X → H, IsReproducingKernelOn F' k') ∧
    ∀ k' k'' : X → H, IsReproducingKernelOn F' k' → IsReproducingKernelOn F'ᗮ k'' →
      ∀ x y : X, k' y x + k'' y x = kernelFn H x y := by sorry

end AronszajnRK.Sum
