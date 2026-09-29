-- Prove2me | Theorems.Thm_AutomorphicForm_hasSum_setIntegral_sigmaCentralizer_of_lintegral_tsum_enorm_lt_top
-- name    : AutomorphicForm.hasSum_setIntegral_sigmaCentralizer_of_lintegral_tsum_enorm_lt_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/f77f85e4-822e-5230-bcb3-61e3783873c1
-- title:
--   Class-by-class expansion of a twisted GL₂ kernel integral
-- statement:
--   Let $K \subseteq L$ be fields with $L$ a number field, let $R$ be a Dedekind domain with $L$ as an $R$-algebra and fraction field, and equip $G_{\mathbb A} = \mathrm{GL}_2$ of the adele ring of $R$, $L$ with a measurable space structure that is Borel for its topology; write $\iota$ for the homomorphism [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15) from $\mathrm{GL}_2(L)$ to $G_{\mathbb A}$ induced by the structure map $L \to \mathbb A$. Let $\sigma$ be a $K$-algebra automorphism of $L$ and $\sigma_{\mathbb A} : G_{\mathbb A} \to G_{\mathbb A}$ a continuous monoid homomorphism with $\sigma_{\mathbb A}(\iota(\gamma)) = \iota(\sigma(\gamma))$ for all $\gamma \in \mathrm{GL}_2(L)$, where $\sigma$ acts entrywise. Let $\mu$ be a measure on $G_{\mathbb A}$ invariant under the action of the subgroup $\iota(\mathrm{GL}_2(L))$, and $\Phi$ a fundamental domain for that subgroup with respect to $\mu$. Let $C$ be a set of $\sigma$-conjugacy classes, i.e. of points of the quotient of $\mathrm{GL}_2(L)$ by the relation [`AutomorphicForm.IsSigmaConj`](def/AutomorphicForm_SigmaConjugacy.html#L15) for $\sigma$, characterised by $\delta_2 = k^{-1}\delta_1\sigma(k)$ for some $k$; let $\mathrm{rep}$ assign to each $c \in C$ an element of $\mathrm{GL}_2(L)$ whose class is $c$, and let $\Psi(c)$, for $c \in C$, be a fundamental domain for the image under $\iota$ of the $\sigma$-twisted centraliser $\{t \in \mathrm{GL}_2(L) : t\,\mathrm{rep}(c)\,\sigma(t)^{-1} = \mathrm{rep}(c)\}$. Let $E$ be a real normed space and $F : G_{\mathbb A} \to E$ strongly measurable, and assume the absolute convergence hypothesis that the lower Lebesgue integral over $\Phi$ of $\sum_{\delta} \|F(x^{-1}\iota(\delta)\sigma_{\mathbb A}(x))\|_e$, the sum running over all $\delta \in \mathrm{GL}_2(L)$ whose $\sigma$-conjugacy class lies in $C$, is finite. Then three conclusions hold: the sum over $c \in C$ of the lower Lebesgue integrals over $\Psi(c)$ of $\|F(x^{-1}\iota(\mathrm{rep}(c))\sigma_{\mathbb A}(x))\|_e$ equals that integral over $\Phi$; for each $c \in C$ the function $x \mapsto F(x^{-1}\iota(\mathrm{rep}(c))\sigma_{\mathbb A}(x))$ is integrable on $\Psi(c)$ for $\mu$; and the family of Bochner integrals $\int_{\Psi(c)} F(x^{-1}\iota(\mathrm{rep}(c))\sigma_{\mathbb A}(x))\,d\mu$, indexed by $c \in C$, has sum $\int_{\Phi} \sum_{\delta} F(x^{-1}\iota(\delta)\sigma_{\mathbb A}(x))\,d\mu$.
--
--   This is the passage, on the geometric side of the twisted trace formula for $\mathrm{GL}_2$, from the integral over a fundamental domain of the $\sigma$-twisted kernel $\sum_\delta F(x^{-1}\delta\,\sigma(x))$ restricted to a family $C$ of $\sigma$-conjugacy classes, to the sum over those classes of global twisted orbital integrals, in the absolutely convergent form that permits the interchange of sum and integral. It is used in the treatment of the classes whose norm is elliptic regular or central, and in the identification of the central-elliptic contribution as a weighted sum of integrals over twisted-centraliser fundamental domains.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_hasSum_setIntegral_sigmaCentralizer_of_lintegral_tsum_enorm_lt_top.lean

import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.hasSum_setIntegral_sigmaCentralizer_of_lintegral_tsum_enorm_lt_top
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (R : Type) [CommRing R] [IsDedekindDomain R] [Algebra R L] [IsFractionRing R L]
    [MeasurableSpace (AutomorphicForm.AdelicGL2 R L)] [BorelSpace (AutomorphicForm.AdelicGL2 R L)]
    (σ : L ≃ₐ[K] L)
    (σA : AutomorphicForm.AdelicGL2 R L →* AutomorphicForm.AdelicGL2 R L) (hσAc : Continuous σA)
    (hσA : ∀ γ : GL (Fin 2) L,
      σA (AutomorphicForm.globalPoints R L γ) =
        AutomorphicForm.globalPoints R L (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ))
    (μ : MeasureTheory.Measure (AutomorphicForm.AdelicGL2 R L))
    [MeasureTheory.SMulInvariantMeasure (AutomorphicForm.globalPoints R L).range
      (AutomorphicForm.AdelicGL2 R L) μ]
    (Φ : Set (AutomorphicForm.AdelicGL2 R L))
    (hΦ : MeasureTheory.IsFundamentalDomain (AutomorphicForm.globalPoints R L).range Φ μ)
    (C : Set (LT.TwistedNorm.SigmaConjClasses σ))
    (rep : LT.TwistedNorm.SigmaConjClasses σ → GL (Fin 2) L)
    (hrep : ∀ c ∈ C, LT.TwistedNorm.SigmaConjClasses.mk σ (rep c) = c)
    (Ψ : LT.TwistedNorm.SigmaConjClasses σ → Set (AutomorphicForm.AdelicGL2 R L))
    (hΨ : ∀ c ∈ C, MeasureTheory.IsFundamentalDomain
      ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (rep c)).map
        (AutomorphicForm.globalPoints R L)) (Ψ c) μ)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : AutomorphicForm.AdelicGL2 R L → E) (hF : MeasureTheory.StronglyMeasurable F)
    (habs : ∫⁻ x in Φ, ∑' δ : {δ : GL (Fin 2) L // LT.TwistedNorm.SigmaConjClasses.mk σ δ ∈ C},
        ‖F (x⁻¹ * AutomorphicForm.globalPoints R L δ * σA x)‖ₑ ∂μ < ⊤) :
    (∑' c : C, ∫⁻ x in Ψ c, ‖F (x⁻¹ * AutomorphicForm.globalPoints R L (rep c) * σA x)‖ₑ ∂μ =
        ∫⁻ x in Φ, ∑' δ : {δ : GL (Fin 2) L // LT.TwistedNorm.SigmaConjClasses.mk σ δ ∈ C},
          ‖F (x⁻¹ * AutomorphicForm.globalPoints R L δ * σA x)‖ₑ ∂μ) ∧
    (∀ c ∈ C, MeasureTheory.IntegrableOn
        (fun x => F (x⁻¹ * AutomorphicForm.globalPoints R L (rep c) * σA x)) (Ψ c) μ) ∧
      HasSum (fun c : C => ∫ x in Ψ c, F (x⁻¹ * AutomorphicForm.globalPoints R L (rep c) * σA x) ∂μ)
        (∫ x in Φ, ∑' δ : {δ : GL (Fin 2) L // LT.TwistedNorm.SigmaConjClasses.mk σ δ ∈ C},
          F (x⁻¹ * AutomorphicForm.globalPoints R L δ * σA x) ∂μ) := by sorry
