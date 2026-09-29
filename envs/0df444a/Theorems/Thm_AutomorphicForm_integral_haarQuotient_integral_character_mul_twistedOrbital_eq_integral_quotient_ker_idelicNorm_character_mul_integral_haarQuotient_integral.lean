-- Prove2me | Theorems.Thm_AutomorphicForm_integral_haarQuotient_integral_character_mul_twistedOrbital_eq_integral_quotient_ker_idelicNorm_character_mul_integral_haarQuotient_integral
-- name    : AutomorphicForm.integral_haarQuotient_integral_character_mul_twistedOrbital_eq_integral_quotient_ker_idelicNorm_character_mul_integral_haarQuotient_integral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/9a90638c-2ce6-5125-aa19-de280a394b27
-- title:
--   Folding a twisted central integral over the norm-one ideles
-- statement:
--   The setting is a Galois extension $L/K$ of number fields ($K$, $L$ fields with `NumberField` instances, `Algebra K L`, `FiniteDimensional K L`, `IsGalois K L`), with the idele ring $\mathbb{A}_L$ of $L$ written `AdeleRing (𝓞 L) L`, its unit group $\mathbb{A}_L^\times$ carrying a measurable space and Borel structure, and $\nu_{Z_L}$ a Haar measure on $\mathbb{A}_L^\times$. The group $G =$ `AdelicGL2 (𝓞 L) L` is $\mathrm{GL}_2(\mathbb{A}_L)$, equipped with the Borel $\sigma$-algebra `glBorel` (a local instance) and the Haar measure `adelicGLHaar (Fin 2) (𝓞 L) L`.
--
--   The further data are: a descent datum $D$ of type [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28), i.e. a homomorphism $\tau \mapsto D.\mathrm{act}\,\tau$ from $\mathrm{Gal}(L/K)$ to ring automorphisms of $\mathbb{A}_L$ which are continuous and compatible with the action on $L$ through `algebraMap`; an element $\sigma \in \mathrm{Gal}(L/K)$ together with the hypothesis `hgen` that every $\tau \in \mathrm{Gal}(L/K)$ lies in `Subgroup.zpowers σ`, so that the Galois group is cyclic with generator $\sigma$; and a homomorphism $\xi_L$ from the top subgroup of $\mathbb{A}_L^\times$ to $\mathbb{C}^\times$, subject to `hξc`, continuity of $z \mapsto \xi_L(z) \in \mathbb{C}$, and `hξσ`, the invariance $\xi_L(D.\mathrm{unitsAct}\,\sigma\,(z)) = \xi_L(z)$ for all $z$, where `unitsAct` is the induced action of $\mathrm{Gal}(L/K)$ on $\mathbb{A}_L^\times$ by multiplicative automorphisms.
--
--   Two subgroups appear. First, $H \le G$ is assumed closed (`hHc`) and is characterised by `hH`: a matrix $h$ lies in $H$ exactly when its $(1,0)$ and $(0,1)$ entries vanish and $\mathrm{sigmaAdelicAct}(h)\,h^{-1}$ lies in the centre of $G$, where `sigmaAdelicAct K L D σ` is the entrywise application of $D.\mathrm{act}\,\sigma$ to matrices; thus $H$ is the stabiliser of the twisted diagonal. It carries a measure $\mu_H$ which is a Haar measure and right invariant. Second, $N_1 \le \mathbb{A}_L^\times$ is assumed closed (`hN1c`) and, by `hN1`, consists exactly of the $z$ with `(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z = 1`, i.e. the kernel of the idelic norm attached to the base change $\mathbb{A}_K \to \mathbb{A}_L$; it carries a Haar measure $\mu_N$. For a subgroup $S$ of a group $\Gamma$, `MulAction.orbitRel.Quotient S Γ` is the quotient by the orbit relation, and [`HaarQuotient.measure μ S μS`](def/HaarQuotient.html#L28) is the image under the quotient map of $\mu$ weighted by the density `density S μS`; representatives are taken via `Quotient.out`.
--
--   Under these hypotheses the conclusion is universally quantified over $t \in \mathrm{GL}_2(L)$ whose $(1,0)$ and $(0,1)$ entries vanish and which is regular in the sense that $N_{L/K}(t_{00}/t_{11}) \neq 1$ (`Algebra.norm K`), and over $\varphi : G \to \mathbb{C}$ continuous with compact support. Here `globalPoints (𝓞 L) L t` is the image of $t$ under the entrywise map induced by $L \to \mathbb{A}_L$, `centralScalar (𝓞 L) L z` is the scalar matrix $z \cdot I_2$, and `adelicWeyl (𝓞 L) L` is the image of $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   The conclusion is a conjunction of two implications.
--
--   The first implication assumes that the function on $H \backslash G$ sending $q$ to
--   $$\int_{\mathbb{A}_L^\times} \xi_L(z)\,\varphi\bigl(q^{-1}\,\iota(t)\,\mathrm{sigmaAdelicAct}(z\cdot I_2 \cdot q)\bigr)\,d\nu_{Z_L}(z)$$
--   (with $q$ the chosen representative and $\iota(t) =$ `globalPoints (𝓞 L) L t`) is integrable for [`HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH`](def/HaarQuotient.html#L28). Its consequent has two parts: (i) the function on the quotient $\mathbb{A}_L^\times / N_1$ sending $w$ to
--   $$\xi_L(w) \int_{H \backslash G} \int_{N_1} \varphi\bigl(q^{-1}\,\iota(t)\,\bigl((n w)\cdot I_2\bigr)\,\mathrm{sigmaAdelicAct}(q)\bigr)\,d\mu_N(n)\,dq$$
--   is integrable for [`HaarQuotient.measure νZL N1 μN`](def/HaarQuotient.html#L28); and (ii) the integral of the first function over $H \backslash G$ equals the integral of the second over $\mathbb{A}_L^\times / N_1$, both quotients carrying the respective [`HaarQuotient.measure`](def/HaarQuotient.html#L28). Note that on the left the twist `sigmaAdelicAct` is applied to the product $z\cdot I_2 \cdot q$, whereas on the right the central scalar $(n w) \cdot I_2$ stands untwisted and `sigmaAdelicAct` is applied to $q$ alone.
--
--   The second implication is the same statement with a real weight inserted. Writing $h(g) =$ [`NumberField.AdelicHeight.adelicHeight L g`](def/NumberField_AdelicHeight.html#L158) (the product of the archimedean height `archHeight` and the finite height `finHeight` of the corresponding components), the weight at a representative $q$ is the real number $-\log h(q) - \log h(\mathrm{adelicWeyl} \cdot q)$, coerced to $\mathbb{C}$. The hypothesis is that $q \mapsto \bigl(-\log h(q) - \log h(\mathrm{adelicWeyl}\cdot q)\bigr)\int_{\mathbb{A}_L^\times} \xi_L(z)\varphi(q^{-1}\iota(t)\,\mathrm{sigmaAdelicAct}(z\cdot I_2\cdot q))\,d\nu_{Z_L}(z)$ is integrable on $H\backslash G$; the consequent asserts (i) integrability on $\mathbb{A}_L^\times/N_1$ of $w \mapsto \xi_L(w)\int_{H\backslash G}\bigl(-\log h(q) - \log h(\mathrm{adelicWeyl}\cdot q)\bigr)\int_{N_1}\varphi\bigl(q^{-1}\iota(t)((nw)\cdot I_2)\,\mathrm{sigmaAdelicAct}(q)\bigr)d\mu_N(n)\,dq$, where the weight sits inside the $H\backslash G$-integral and outside the $N_1$-integral, and (ii) the equality of the corresponding two iterated integrals. No proportionality constant occurs: both identities have constant $1$.
--
--   This is the first step of the centre-unfolding of the hyperbolic (regular semisimple) terms in the twisted trace formula for a cyclic extension $L/K$: the integral over $H\backslash G$ of a $\sigma$-twisted orbital integral against the central character $\xi_L$ is refolded as an integral over the idele classes modulo the norm-one subgroup $N^1 = \ker N_{L/K}$, the point being that $\xi_L$ is trivial on $N^1$ by idelic Hilbert 90 for the cyclic group generated by $\sigma$. Both the unweighted and the height-weighted versions are recorded, since the weighted form is what the truncated (Arthur-style) twisted trace formula needs; the result feeds into the evaluation of twisted orbital integrals up to an explicit constant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_haarQuotient_integral_character_mul_twistedOrbital_eq_integral_quotient_ker_idelicNorm_character_mul_integral_haarQuotient_integral.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.integral_haarQuotient_integral_character_mul_twistedOrbital_eq_integral_quotient_ker_idelicNorm_character_mul_integral_haarQuotient_integral
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξσ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξL ⟨D.unitsAct σ z, Subgroup.mem_top _⟩ = ξL ⟨z, Subgroup.mem_top z⟩)

    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (N1 : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hN1c : IsClosed (N1 : Set (AdeleRing (𝓞 L) L)ˣ))
    (hN1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ N1 ↔
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z = 1)
    (μN : Measure N1) [μN.IsHaarMeasure] :
    ∀ (t : GL (Fin 2) L), (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 → (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 →
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1 →
    ∀ (φ : AdelicGL2 (𝓞 L) L → ℂ), Continuous φ → HasCompactSupport φ →

    (Integrable (fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) =>
            (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL))
        (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) →
      Integrable (fun wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ =>
          ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
          (∫ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
            (∫ n : N1, φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                (AutomorphicForm.centralScalar (𝓞 L) L ((n : (AdeleRing (𝓞 L) L)ˣ) * wq.out) *
                  AutomorphicForm.sigmaAdelicAct K L D σ ((q.out : AdelicGL2 (𝓞 L) L)))) ∂μN)
          ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)))
        (HaarQuotient.measure νZL N1 μN) ∧
      ∫ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
            (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL)
          ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) =
        ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
          ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
          (∫ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
            (∫ n : N1, φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                (AutomorphicForm.centralScalar (𝓞 L) L ((n : (AdeleRing (𝓞 L) L)ˣ) * wq.out) *
                  AutomorphicForm.sigmaAdelicAct K L D σ ((q.out : AdelicGL2 (𝓞 L) L)))) ∂μN)
          ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH))
          ∂(HaarQuotient.measure νZL N1 μN)) ∧

    (Integrable (fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) =>
            ((-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))) : ℝ) : ℂ) * (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL))
        (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) →
      Integrable (fun wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ =>
          ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
          (∫ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
            ((-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))) : ℝ) : ℂ) *
            (∫ n : N1, φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                (AutomorphicForm.centralScalar (𝓞 L) L ((n : (AdeleRing (𝓞 L) L)ˣ) * wq.out) *
                  AutomorphicForm.sigmaAdelicAct K L D σ ((q.out : AdelicGL2 (𝓞 L) L)))) ∂μN)
          ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)))
        (HaarQuotient.measure νZL N1 μN) ∧
      ∫ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
            ((-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))) : ℝ) : ℂ) * (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL)
          ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) =
        ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
          ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
          (∫ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
            ((-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))) : ℝ) : ℂ) *
            (∫ n : N1, φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                (AutomorphicForm.centralScalar (𝓞 L) L ((n : (AdeleRing (𝓞 L) L)ˣ) * wq.out) *
                  AutomorphicForm.sigmaAdelicAct K L D σ ((q.out : AdelicGL2 (𝓞 L) L)))) ∂μN)
          ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH))
          ∂(HaarQuotient.measure νZL N1 μN)) := by sorry
