-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_mul_pseudoEisenstein_eq_integral_rationalTorusUnipotentQuotient_constantTerm_mul
-- name    : AutomorphicForm.setIntegral_mul_pseudoEisenstein_eq_integral_rationalTorusUnipotentQuotient_constantTerm_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/d919ee5f-7791-5940-9e02-10a5f250c119
-- title:
--   Unfolding a pseudo-Eisenstein series against an automorphic function
-- statement:
--   Let $F$ be a number field, write $\mathbb{A}$ for its adele ring and $G(\mathbb{A})=\mathrm{GL}_2(\mathbb{A})$, and let `globalPoints` denote the homomorphism $\mathrm{GL}_2(F)\to G(\mathbb{A})$ induced by $F\to\mathbb{A}$, both groups carrying the Borel $\sigma$-algebra and $G(\mathbb{A})$ the Haar measure `adelicGLHaar`. Let $S\subseteq G(\mathbb{A})$ be measurable and stable under left multiplication by every $\mathrm{GL}_2(F)$-point and by every $n(u)=\begin{pmatrix}1&u\\0&1\end{pmatrix}$, $u\in\mathbb{A}$, and let $\Phi_0\subseteq S$ be a fundamental domain for the range of `globalPoints` with respect to the restriction of Haar measure to $S$. Let $f,\psi:G(\mathbb{A})\to\mathbb{C}$ be measurable with $f$ left invariant under all $\mathrm{GL}_2(F)$-points, and $\psi$ left invariant under the image of $\{\gamma\in \mathrm{GL}_2(F):\gamma_{10}=0\}$ and under all $n(u)$, $u\in\mathbb{A}$. Assume $\int^{-}_{\Phi_0}\lVert f(x)\rVert\bigl(\lVert\psi(x)\rVert+\sum_{\xi\in F}\lVert\psi(w\,n(\xi)x)\rVert\bigr)\,dx<\infty$ in $[0,\infty]$, where $w$ is the image of $\begin{pmatrix}0&1\\1&0\end{pmatrix}$. Put $E_\psi(g)=\psi(g)+\sum_{\beta\in F}\psi(w\,n(\beta)g)$, let $f_N(y)=\int f(n(t)y)\,d\mu(t)$ with $\mu$ the adelic additive Haar measure conditioned on the box `adelicBox F`, and set $R=\mathbf{1}_S\cdot(f_N\cdot\psi)$. Then: $f\cdot E_\psi$ is integrable on $\Phi_0$; $R(hy)=R(y)$ for every $h$ in the join $H$ of `rationalCentre F`, `rationalDiagOne F` and the group of adelic unipotents and every $y$; the function $q\mapsto R(q.\mathrm{out})$ on the orbit quotient $H\backslash G(\mathbb{A})$ is integrable for `rationalTorusUnipotentQuotientMeasure F`; and $\int_{\Phi_0}f\cdot E_\psi = \int R(q.\mathrm{out})\,dq$.
--
--   This is the Rankin–Selberg unfolding identity on $\mathrm{GL}_2$ over a number field, formulated on a $G(F)$- and $N(\mathbb{A})$-stable region $S$ (for instance a determinant slab) so that no central character enters: the pairing of an automorphic function with a pseudo-Eisenstein series on a fundamental domain equals the pairing of its constant term with the inducing profile over $T(F)N(\mathbb{A})\backslash G(\mathbb{A})$. It is used by the slab-pairing and Maass–Selberg computations for truncated Eisenstein series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_mul_pseudoEisenstein_eq_integral_rationalTorusUnipotentQuotient_constantTerm_mul.lean

import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_AutomorphicForm_BorelSubgroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem AutomorphicForm.setIntegral_mul_pseudoEisenstein_eq_integral_rationalTorusUnipotentQuotient_constantTerm_mul
    (F : Type) [Field F] [NumberField F]
    (S : Set (AdelicGL2 (𝓞 F) F)) (hSm : MeasurableSet S)
    (hS : ∀ (γ : GL (Fin 2) F) (x : AdelicGL2 (𝓞 F) F), globalPoints (𝓞 F) F γ * x ∈ S ↔ x ∈ S)
    (hSN : ∀ (u : AdeleRing (𝓞 F) F) (x : AdelicGL2 (𝓞 F) F), unipotentGL2 u * x ∈ S ↔ x ∈ S)
    (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (hΦ₀S : Φ₀ ⊆ S)
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀ ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S))
    (f ψ : AdelicGL2 (𝓞 F) F → ℂ) (hf : Measurable f) (hψ : Measurable ψ)
    (hfG : ∀ (γ : GL (Fin 2) F) (x : AdelicGL2 (𝓞 F) F), f (globalPoints (𝓞 F) F γ * x) = f x)
    (hψB : ∀ γ ∈ borelSubgroup F, ∀ x : AdelicGL2 (𝓞 F) F, ψ (globalPoints (𝓞 F) F γ * x) = ψ x)
    (hψN : ∀ (u : AdeleRing (𝓞 F) F) (x : AdelicGL2 (𝓞 F) F), ψ (unipotentGL2 u * x) = ψ x)
    (hfin : ∫⁻ x in Φ₀, ‖f x‖ₑ * (‖ψ x‖ₑ + ∑' ξ : F,
        ‖ψ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x)‖ₑ)
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ∞) :
    IntegrableOn (fun x => f x * pseudoEisenstein F ψ x) Φ₀ (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
    (∀ h ∈ rationalTorusUnipotent F, ∀ y : AdelicGL2 (𝓞 F) F,
      S.indicator (fun y => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
          (fun t => unipotentGL2 t) f y * ψ y) (h * y) =
        S.indicator (fun y => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
          (fun t => unipotentGL2 t) f y * ψ y) y) ∧
    Integrable (fun q : RationalTorusUnipotentQuotient F =>
        S.indicator (fun y => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
          (fun t => unipotentGL2 t) f y * ψ y) q.out)
      (rationalTorusUnipotentQuotientMeasure F) ∧
    ∫ x in Φ₀, f x * pseudoEisenstein F ψ x ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
      ∫ q, S.indicator (fun y => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
          (fun t => unipotentGL2 t) f y * ψ y) q.out ∂(rationalTorusUnipotentQuotientMeasure F) := by sorry
