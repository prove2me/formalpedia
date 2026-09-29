-- Prove2me | Theorems.Thm_AutomorphicForm_summable_norm_godementSection_bruhat_and_norm_add_tsum_norm_le_mul_setIntegral_tsum_norm_of_lintegral_tsum_enorm_lt_top
-- name    : AutomorphicForm.summable_norm_godementSection_bruhat_and_norm_add_tsum_norm_le_mul_setIntegral_tsum_norm_of_lintegral_tsum_enorm_lt_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/3278b93a-d5f6-5241-9676-e0e02b3ab19e
-- title:
--   Absolute majorisation of the Bruhat series of a Godement section
-- statement:
--   Let $F$ be a number field, and equip the idele units $(\mathbb{A}_F)^\times$ (the units of `AdeleRing (𝓞 F) F`) with a measurable structure that is the Borel structure. Let $\nu_0$ be a left-invariant measure on $(\mathbb{A}_F)^\times$ and let $\Omega$ be a $\nu_0$-fundamental domain for the action of the range of the map on units induced by $F \to \mathbb{A}_F$, i.e. of the principal ideles. Let $\mu, \nu : (\mathbb{A}_F)^\times \to \mathbb{C}^\times$ be monoid homomorphisms that are unitary in the sense that all their values have complex absolute value $1$, let $\alpha : (\mathbb{A}_F)^\times \to \mathbb{R}^\times$ be a monoid homomorphism with $\alpha(x) > 0$ for all $x$, let $\Phi : \mathbb{A}_F^2 \to \mathbb{C}$ be continuous, $s \in \mathbb{C}$ and $g \in \mathrm{GL}_2(\mathbb{A}_F)$. Write $\|t\| =$ `ideleNorm F t` for the value at $t$ of the distributive Haar character of $\mathbb{A}_F$, $\chi = \mu\nu^{-1}$, and let $f_s$ denote `godementSection F ν₀ μ ν α hα Φ s`, so that $f_s(h) = \mu(\det h)\,\alpha(\det h)^{s+1/2} \int \Phi\bigl(t\cdot(\text{bottom row of } h)\bigr)\chi(t)\,\|t\|^{2s+1}\,d\nu_0(t)$, the power of $\alpha(\det h)$ being the complex power of its positive real value. Assume the finiteness hypothesis that the lower Lebesgue integral over $\Omega$ of $t \mapsto \sum_{\xi \in F^2 \smallsetminus \{0\}} \bigl\|\Phi\bigl(t\cdot \xi g\bigr)\,\chi(t)\,\|t\|^{2s+1}\bigr\|_e$ is $< \infty$, where $\xi g$ means the row vector $\xi$, pushed into $\mathbb{A}_F^2$, multiplied on the right by the matrix of $g$. Then, with $w$ the image in $\mathrm{GL}_2(\mathbb{A}_F)$ of $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $n(\xi) = \begin{pmatrix}1&\xi\\0&1\end{pmatrix}$, the family $\xi \mapsto \|f_s(w\,n(\xi)\,g)\|$ indexed by $\xi \in F$ is summable, and $$\|f_s(g)\| + \sum_{\xi \in F} \|f_s(w\,n(\xi)\,g)\| \le \alpha(\det g)^{\operatorname{Re} s + 1/2} \int_\Omega \Bigl(\sum_{\xi \in F^2 \smallsetminus \{0\}} \|\Phi(t\cdot \xi g)\|\Bigr)\,\|t\|^{2\operatorname{Re} s + 1}\,d\nu_0(t),$$ the exponents here being real powers of positive reals.
--
--   This is the absolute-value form of the Bruhat-cell unfolding of a Godement section for $\mathrm{GL}_2$ over a number field: the value at the identity coset together with the values along the big cell $w\,n(\xi)$ is dominated by the corresponding Epstein-type integral of $|\Phi|$ over a fundamental domain for the principal ideles, the unitary character $\chi$ and $\mu(\det g)$ disappearing in absolute value. It feeds the summability statement for Schwartz–Bruhat $\Phi$ in the right half-plane $\operatorname{Re} s > 1/2$ and the uniform bound on Siegel sets used in the Rankin–Selberg estimates of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_summable_norm_godementSection_bruhat_and_norm_add_tsum_norm_le_mul_setIntegral_tsum_norm_of_lintegral_tsum_enorm_lt_top.lean

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WeylIntertwining

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.TateGlobal AutomorphicForm

theorem AutomorphicForm.summable_norm_godementSection_bruhat_and_norm_add_tsum_norm_le_mul_setIntegral_tsum_norm_of_lintegral_tsum_enorm_lt_top
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsMulLeftInvariant]
    (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν₀)
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (hΦ : Continuous Φ)
    (s : ℂ) (g : AdelicGL2 (𝓞 F) F)
    (habs : ∫⁻ t in Ω, ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
        ‖Φ ((t : AdeleRing (𝓞 F) F) •
              Matrix.vecMul (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))
                (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
          * (((μ * ν⁻¹) t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (2 * s + 1)‖ₑ ∂ν₀ < ⊤) :
    Summable (fun ξ : F => ‖godementSection F ν₀ μ ν α hα Φ s
        (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖) ∧
    ‖godementSection F ν₀ μ ν α hα Φ s g‖
        + ∑' ξ : F, ‖godementSection F ν₀ μ ν α hα Φ s
            (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖
      ≤ ((α (Matrix.GeneralLinearGroup.det g) : ℝˣ) : ℝ) ^ (s.re + 1 / 2)
        * ∫ t in Ω, (∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
            ‖Φ ((t : AdeleRing (𝓞 F) F) •
                  Matrix.vecMul (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))
                    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))‖)
              * (ideleNorm F t) ^ (2 * s.re + 1) ∂ν₀ := by sorry
