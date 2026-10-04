-- Prove2me | Theorems.Thm_AronszajnRK_Product_functional_completion_theorem
-- name    : AronszajnRK.Product.functional_completion_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:50:24.984022+00:00
-- url     : https://prove2.me/theorems/e4bad637-0e46-489e-8359-1b2252e9bee6
-- title:
--   §4, Theorem — existence and uniqueness of the functional completion
-- statement:
--   Let $F$ be a class of complex-valued functions on a set $E$ forming a Hilbert space except possibly for completeness. A functional completion of $F$ exists if and only if
--
--   1. for every fixed $y \in E$ the linear functional $f \mapsto f(y)$ on $F$ is bounded: there is $M_y$ with $|f(y)| \le M_y \|f\|$ for all $f \in F$;
--   2. for every Cauchy sequence $(f_m) \subset F$, the condition $f_m(y) \to 0$ for every $y \in E$ implies $\|f_m\| \to 0$.
--
--   Moreover, if a functional completion exists it is unique: any two functional completions consist of the same functions, and each function has the same norm in both:
--
--   $$
--   \overline{F}_1 = \overline{F}_2 \ \text{as classes of functions}, \qquad \|f\|_{\overline F_1} = \|f\|_{\overline F_2}.
--   $$
--
--   This theorem is used in §8 to show that the direct product $F_1 \otimes F_2$ is well defined.
--
--   **Formalization Note** $F$ is an inner product space $G$ with an injective linear map $\iota$ into functions on $E$. The paper calls $F$ "incomplete"; its statement only uses that completeness is not assumed, so completeness of $G$ is neither assumed nor excluded. Existence quantifies over Hilbert spaces in the universe of $G$.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 347, §4, Theorem

import Mathlib
import Definitions.Def_AronszajnRK_Product_IsFunctionalCompletion

open Filter Topology

namespace AronszajnRK.Product

universe u v

/-- N. Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §4,
Theorem, p. 347 (PDF p. 11). A class of functions `F` on `X` forming an incomplete Hilbert space
(here: a complex inner product space `G` with an injective linear map `ι` to functions) has a
functional completion if and only if 1° every evaluation `g ↦ (ι g)(y)` is a bounded linear
functional, and 2° for a Cauchy sequence `(gₘ)` in `G`, `(ι gₘ)(y) → 0` for every `y` implies
`‖gₘ‖ → 0`. If the functional completion is possible, it is unique: any two functional
completions consist of the same functions with the same norms.
Reading decision: completeness of `G` is neither assumed nor excluded (the page's "incomplete"
means "with the exception of the completeness", p. 347). -/
theorem functional_completion_theorem {X : Type u} {G : Type v} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] (ι : G →ₗ[ℂ] (X → ℂ)) (hι : Function.Injective ι) :
    ((∃ (H : Type v) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : CompleteSpace H) (_ : RKHS ℂ H X ℂ), IsFunctionalCompletion ι H) ↔
      ((∀ y : X, ∃ M : ℝ, ∀ g : G, ‖ι g y‖ ≤ M * ‖g‖) ∧
        (∀ g : ℕ → G, CauchySeq g → (∀ y : X, Tendsto (fun m => ι (g m) y) atTop (𝓝 0)) →
          Tendsto (fun m => ‖g m‖) atTop (𝓝 0)))) ∧
    (∀ (H₁ : Type*) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
        [RKHS ℂ H₁ X ℂ] (H₂ : Type*) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
        [CompleteSpace H₂] [RKHS ℂ H₂ X ℂ],
      IsFunctionalCompletion ι H₁ → IsFunctionalCompletion ι H₂ →
        Set.range (fun f : H₁ => (⇑f : X → ℂ)) = Set.range (fun f : H₂ => (⇑f : X → ℂ)) ∧
        ∀ (f₁ : H₁) (f₂ : H₂), (⇑f₁ : X → ℂ) = ⇑f₂ → ‖f₁‖ = ‖f₂‖) := by sorry

end AronszajnRK.Product
