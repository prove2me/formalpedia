-- Prove2me | Theorems.Thm_AronszajnRK_Inclusion_intersection_closed_transformation
-- name    : AronszajnRK.Inclusion.intersection_closed_transformation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:29:37.182153+00:00
-- url     : https://prove2.me/theorems/a9abe62a-9e26-4e52-8a90-f1a2e405d669
-- title:
--   §13 (C), Lemma — the identity correspondence $F_1\cdot F_2 \to F_2$ is closed
-- statement:
--   Let $F_1$ and $F_2$ be classes of complex functions on $X$ with reproducing kernels (complex Hilbert spaces with norms $\|\cdot\|_1$, $\|\cdot\|_2$), and let $F_0 = F_1\cdot F_2$ be their intersection. The correspondence
--
--   $$T : F_0\subset F_1 \longrightarrow F_2, \qquad f \text{ (as element of } F_1) \mapsto f \text{ (as element of } F_2),$$
--
--   is a closed linear transformation: if $f_n\in F_0$, $f_n\to f'$ in $F_1$ and $f_n\to f''$ in $F_2$, then $f'\in F_0$ and $f'' = f'$.
--
--   Combined with Banach's closed graph theorem, this lemma is what makes any inclusion of (R.K.)-classes automatically bounded.
--
--   **Formalization Note** $F_0$ is the linear subspace of $H_1$ consisting of the elements whose function belongs to $H_2$; $T$ is required to send each such element to the element of $H_2$ with the same function; "closed" is the paper's sequential definition `IsClosedTransformation`.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 382, §13 (C), Lemma

import Mathlib
import Definitions.Def_AronszajnRK_Inclusion_IsClosedTransformation

namespace AronszajnRK.Inclusion

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §13 (C), Lemma,
p. 382 (PDF p. 46). Let `F₁` and `F₂` be classes with reproducing kernels and let `F₀` be their
intersection `F₁ · F₂`. The correspondence transforming `f ∈ F₀` considered as belonging to `F₁`
into `f` considered as belonging to `F₂` is a closed linear transformation.

`F₀`, as a linear subspace of `H₁`, is the preimage under `f ↦ ⇑f` of the set of functions of
`H₂`; the correspondence `T` sends `f` to the element of `H₂` with the same function; "closed" is
the paper's sequential notion `IsClosedTransformation` (p. 382). -/
theorem intersection_closed_transformation {X H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [RKHS ℂ H₁ X ℂ]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [RKHS ℂ H₂ X ℂ] :
    ∃ T : (LinearMap.range ((RKHS.coeCLM ℂ : H₂ →L[ℂ] X → ℂ) : H₂ →ₗ[ℂ] X → ℂ)).comap
        ((RKHS.coeCLM ℂ : H₁ →L[ℂ] X → ℂ) : H₁ →ₗ[ℂ] X → ℂ) →ₗ[ℂ] H₂,
      (∀ f, ⇑(T f) = ⇑(f : H₁)) ∧ IsClosedTransformation T := by sorry

end AronszajnRK.Inclusion
