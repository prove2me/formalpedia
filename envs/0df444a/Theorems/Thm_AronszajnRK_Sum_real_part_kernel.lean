-- Prove2me | Theorems.Thm_AronszajnRK_Sum_real_part_kernel
-- name    : AronszajnRK.Sum.real_part_kernel
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:49:28.380178+00:00
-- url     : https://prove2.me/theorems/55b38ac7-b92d-4644-bd2d-a3896a51da63
-- title:
--   §6, p. 354, Eq. (1) — the conjugate class has kernel K(y, x), and Re K is the kernel of {f + ḡ}
-- statement:
--   Let $F$ be a complex Hilbert space of functions on a set $E$ with reproducing kernel $K$. Then:
--
--   1. every complex Hilbert space $\bar F$ of functions on $E$ with reproducing kernel $K_1(x,y)=K(y,x)=\overline{K(x,y)}$ consists exactly of the conjugates $\bar f$ of the functions $f\in F$, with $\|\bar f\|_1=\|f\|$;
--   2. there is a complex Hilbert space of functions on $E$ with reproducing kernel
--   $$\operatorname{Re}K(x,y)=2^{-1}\big(K(x,y)+K(y,x)\big);$$
--   3. every such space $F_0$ consists exactly of the sums $\varphi=f+\bar g$ with $f,g\in F$, and
--   $$\|\varphi\|_0^2=2\min\big[\|f\|^2+\|g\|^2\big],$$
--   the minimum (attained) being taken over all decompositions $\varphi=f+\bar g$ with $f,g\in F$.
--
--   This is the sum theorem applied to the kernels $\tfrac12K$ and $\tfrac12\bar K$; it shows how the real part of a kernel corresponds to a class of functions closed under conjugation.
--
--   **Formalization Note** The paper's remark that in $\bar F$ the scalar product is $(\bar f,\bar g)_1=(g,f)$ follows from the norm equality by polarization and is not stated separately. Conjugation of functions is pointwise `star`. "min" is an attained minimum (`IsLeast`).
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 354, §6, Eq. (1)

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn

namespace AronszajnRK.Sum

universe u w

/-- **The conjugate class and the kernel `Re K`** (Aronszajn, *Theory of Reproducing Kernels*,
Trans. Amer. Math. Soc. 68 (1950), §6, p. 354 (PDF 18), Eq. (1)). If `F̄` is the class of all
conjugate functions of functions of `F`, the kernel of `F̄` is `K₁(x, y) = \overline{K(x, y)} =
K(y, x)`, with `‖f̄‖₁ = ‖f‖`. Consequently `Re K(x, y) = 2⁻¹(K(x, y) + K(y, x))` is the reproducing
kernel of the class `F₀` of all sums `f + ḡ`, for `f` and `g` in `F`, with the norm
`‖φ‖₀² = 2 min [‖f‖² + ‖g‖²]`, the minimum taken for all decompositions `φ = f + ḡ`.

Shape: (1) every RKHS `H'` with scalar kernel `K(y, x)` consists of the conjugates of the functions
of `H`, and the conjugate of `f` has norm `‖f‖`; (2) some RKHS has scalar kernel
`2⁻¹(K(x, y) + K(y, x))`; (3) every RKHS `H₀` with that kernel consists of the sums `f + ḡ`, and
`‖φ‖₀²` is the attained minimum of `2(‖f‖² + ‖g‖²)`. -/
theorem real_part_kernel {X : Type u}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [RKHS ℂ H X ℂ] :
    (∀ (H' : Type w) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      [RKHS ℂ H' X ℂ], kernelFn H' = (fun x y => kernelFn H y x) →
        Set.range (fun g : H' => (g : X → ℂ)) =
            {h : X → ℂ | ∃ f : H, h = fun x => star (f x)} ∧
        ∀ (g : H') (f : H), (g : X → ℂ) = (fun x => star (f x)) → ‖g‖ = ‖f‖) ∧
    (∃ (H₀ : Type u) (_ : NormedAddCommGroup H₀) (_ : InnerProductSpace ℂ H₀)
        (_ : CompleteSpace H₀) (_ : RKHS ℂ H₀ X ℂ),
        kernelFn H₀ = fun x y => 2⁻¹ * (kernelFn H x y + kernelFn H y x)) ∧
    ∀ (H₀ : Type w) [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀] [CompleteSpace H₀]
      [RKHS ℂ H₀ X ℂ], kernelFn H₀ = (fun x y => 2⁻¹ * (kernelFn H x y + kernelFn H y x)) →
        Set.range (fun φ : H₀ => (φ : X → ℂ)) =
            {h : X → ℂ | ∃ f g : H, h = fun x => f x + star (g x)} ∧
        ∀ φ : H₀, IsLeast
          {r : ℝ | ∃ f g : H, (φ : X → ℂ) = (fun x => f x + star (g x)) ∧
            r = 2 * (‖f‖ ^ 2 + ‖g‖ ^ 2)}
          (‖φ‖ ^ 2) := by sorry

end AronszajnRK.Sum
