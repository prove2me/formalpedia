-- Prove2me | Theorems.Thm_AronszajnRK_Inclusion_kernel_of_contractive_subclass
-- name    : AronszajnRK.Inclusion.kernel_of_contractive_subclass
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:29:15.320377+00:00
-- url     : https://prove2.me/theorems/8e69e631-a9db-4c6c-9a5c-6433d184692e
-- title:
--   §7, Theorem II — a contractively included Hilbert subclass has a kernel $K_1 \ll K$
-- statement:
--   Let $K$ be the reproducing kernel of a class $F$ of complex functions on $X$ with norm $\|\cdot\|$. Suppose the linear class $F_1\subset F$ forms a complex Hilbert space with a norm $\|\cdot\|_1$ such that
--
--   $$\|f_1\|_1 \ \ge\ \|f_1\| \qquad\text{for every } f_1\in F_1 .$$
--
--   Then $F_1$ possesses a reproducing kernel $K_1$, that is, functions $K_1(\cdot,y)\in F_1$ with $f_1(y) = (f_1, K_1(\cdot,y))_1$ for all $f_1\in F_1$ and $y\in X$, and this kernel satisfies $K_1\ll K$.
--
--   This is the necessity half of the inclusion criterion for contractive inclusions; with Theorem I of §7 it characterizes the contractively included subclasses by the order $\ll$.
--
--   **Formalization Note** $F_1$ is not assumed to have a reproducing kernel (that is the conclusion): it is an abstract complex Hilbert space $H_1$ with an injective linear map $\iota$ into functions on $X$, every $\iota f_1$ being a function of $F$. With Mathlib's convention (inner product conjugate-linear in the first slot) the reproducing property is $\langle k_1(y), f_1\rangle = (\iota f_1)(y)$, and $K_1(x,y) = (\iota\, k_1(y))(x)$.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 355, §7, Theorem II

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn
import Definitions.Def_AronszajnRK_Limits_KernelLE

namespace AronszajnRK.Inclusion

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §7, Theorem II,
p. 355 (PDF p. 19). If `K` is the reproducing kernel of the class `F` with the norm `‖ ‖`, and if
the linear class `F₁ ⊂ F` forms a Hilbert space with the norm `‖ ‖₁` such that `‖f₁‖₁ ≥ ‖f₁‖` for
every `f₁ ∈ F₁`, then `F₁` possesses a reproducing kernel `K₁` satisfying `K₁ ≪ K`.

`F₁` is not assumed to be an RKHS: it is a complex Hilbert space `H₁` realized as a class of
functions by an injective linear map `ι : H₁ → (X → ℂ)` with values in `F`. The conclusion gives
the kernel functions `k₁ y = K₁(·, y) ∈ F₁` with the reproducing property
`f₁(y) = (f₁, K₁(·, y))₁` (Mathlib's inner product is conjugate-linear in the first slot, so this is
`⟪k₁ y, f₁⟫_ℂ = ι f₁ y`) and `K₁(x, y) = ι (k₁ y) x` with `K₁ ≪ K`. -/
theorem kernel_of_contractive_subclass {X H H₁ : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    (ι : H₁ →ₗ[ℂ] (X → ℂ)) (hι : Function.Injective ι)
    (hsub : ∀ f₁ : H₁, ∃ f : H, ⇑f = ι f₁)
    (hnorm : ∀ (f₁ : H₁) (f : H), ⇑f = ι f₁ → ‖f‖ ≤ ‖f₁‖) :
    ∃ k₁ : X → H₁, (∀ (y : X) (f₁ : H₁), inner ℂ (k₁ y) f₁ = ι f₁ y) ∧
      AronszajnRK.Limits.KernelLE (fun x y => ι (k₁ y) x) (AronszajnRK.Sum.kernelFn H) := by sorry

end AronszajnRK.Inclusion
