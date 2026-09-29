-- Prove2me | Theorems.Thm_AutomorphicForm_summable_godementSection_and_bruhatSeries_eq_mul_setIntegral_tsum_of_lintegral_tsum_enorm_lt_top
-- name    : AutomorphicForm.summable_godementSection_and_bruhatSeries_eq_mul_setIntegral_tsum_of_lintegral_tsum_enorm_lt_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/18f13329-2492-5653-9b39-6a027463bac7
-- title:
--   Bruhat unfolding of a Godement section into an Epstein integral
-- statement:
--   Let $F$ be a number field, $\mathbb{A}=\mathbb{A}_F$ its adele ring, and equip the idele group $\mathbb{A}^\times$ with a measurable structure that is the Borel structure. Let $\nu_0$ be a left-invariant measure on $\mathbb{A}^\times$ and let $\Omega\subseteq\mathbb{A}^\times$ be a $\nu_0$-fundamental domain for the image subgroup of the principal ideles, i.e. the range of the map induced on units by $F\to\mathbb{A}$. Let $\mu,\nu\colon\mathbb{A}^\times\to\mathbb{C}^\times$ be group homomorphisms with $\mu(\iota(u))=\nu(\iota(u))=1$ for every $u\in F^\times$ and with continuous complex values, let $\alpha\colon\mathbb{A}^\times\to\mathbb{R}^\times$ be a homomorphism with $\alpha(x)>0$ for all $x$, let $\Phi\colon\mathbb{A}^2\to\mathbb{C}$ be continuous, $s\in\mathbb{C}$ and $g\in GL_2(\mathbb{A})$. Write $\chi=\mu\nu^{-1}$, $\|t\|$ for the idele norm of $t$ (the value of the distributive Haar character of $\mathbb{A}$ at $t$), and, for $\xi\in F^2$, let $\xi g$ denote the row vector $\iota(\xi)$ multiplied on the right by $g$. Assume the absolute convergence hypothesis that the lower Lebesgue integral over $\Omega$ of $\sum_{\xi\in F^2\setminus\{0\}}\|\Phi(t\cdot \xi g)\,\chi(t)\,\|t\|^{2s+1}\|_{e}$ against $\nu_0$ is finite. Here the Godement section is $f_s(h)=\mu(\det h)\,\alpha(\det h)^{s+1/2}\int_{\mathbb{A}^\times}\Phi(t\,(h_{1,0},h_{1,1}))\,\chi(t)\,\|t\|^{2s+1}\,d\nu_0(t)$, with $w=\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$ the adelic Weyl and unipotent elements. The conclusion is threefold: the family $\xi\mapsto f_s(w\,n(\iota(\xi))\,g)$ indexed by $\xi\in F$ is summable; the function $t\mapsto\sum_{\xi\in F^2\setminus\{0\}}\Phi(t\cdot \xi g)\,\chi(t)\,\|t\|^{2s+1}$ is integrable on $\Omega$ for $\nu_0$; and $$f_s(g)+\sum_{\xi\in F}f_s(w\,n(\iota(\xi))\,g)=\mu(\det g)\,\alpha(\det g)^{s+1/2}\int_{\Omega}\sum_{\xi\in F^2\setminus\{0\}}\Phi(t\cdot \xi g)\,\chi(t)\,\|t\|^{2s+1}\,d\nu_0(t),$$ the power of $\alpha(\det g)$ being the complex power $\alpha(\det g)^{s+1/2}$.
--
--   This is the unfolding step for Eisenstein series built from Godement sections on $GL_2$: the Bruhat decomposition splits the sum over $B(F)\backslash GL_2(F)$ into the identity coset and the big cell $\{w\,n(\xi)\}_{\xi\in F}$, whose bottom rows $(0,1)g$ and $(1,\xi)g$ have $F^\times$-orbits partitioning $F^2\setminus\{0\}$, so that the Bruhat series becomes a single Epstein-type integral over a fundamental domain for the idele classes. It is used in the Rankin–Selberg part of the Langlands–Tunnell argument, in the results producing entire continuations of Godement–Eisenstein integrals minus their polar parts, with uniform Siegel bounds, for Schwartz–Bruhat data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_summable_godementSection_and_bruhatSeries_eq_mul_setIntegral_tsum_of_lintegral_tsum_enorm_lt_top.lean

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WeylIntertwining

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.TateGlobal AutomorphicForm

theorem AutomorphicForm.summable_godementSection_and_bruhatSeries_eq_mul_setIntegral_tsum_of_lintegral_tsum_enorm_lt_top
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsMulLeftInvariant]
    (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν₀)
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsIdeleClassChar (𝓞 F) F μ) (hν : IsIdeleClassChar (𝓞 F) F ν)
    (hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (hΦ : Continuous Φ)
    (s : ℂ) (g : AdelicGL2 (𝓞 F) F)
    (habs : ∫⁻ t in Ω, ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
        ‖Φ ((t : AdeleRing (𝓞 F) F) •
              Matrix.vecMul (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))
                (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
          * (((μ * ν⁻¹) t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (2 * s + 1)‖ₑ ∂ν₀ < ⊤) :
    Summable (fun ξ : F => godementSection F ν₀ μ ν α hα Φ s
        (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
    IntegrableOn (fun t : (AdeleRing (𝓞 F) F)ˣ => ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
        Φ ((t : AdeleRing (𝓞 F) F) •
              Matrix.vecMul (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))
                (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
          * (((μ * ν⁻¹) t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (2 * s + 1)) Ω ν₀ ∧
    godementSection F ν₀ μ ν α hα Φ s g
        + ∑' ξ : F, godementSection F ν₀ μ ν α hα Φ s
            (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)
      = ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
        * ((cpowChar α hα (s + 1 / 2) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
        * ∫ t in Ω, ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
            Φ ((t : AdeleRing (𝓞 F) F) •
                  Matrix.vecMul (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))
                    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
              * (((μ * ν⁻¹) t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (2 * s + 1) ∂ν₀ := by sorry
