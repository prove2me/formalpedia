-- Prove2me | Theorems.Thm_AutomorphicForm_TwistedBruhat_integral_iwasawa_tsum_normOneFibre_eq_integral_unitFibre_of_fibrewise
-- name    : AutomorphicForm.TwistedBruhat.integral_iwasawa_tsum_normOneFibre_eq_integral_unitFibre_of_fibrewise
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/62d3fb6c-b0a8-55f5-a55a-e819b4d8b02f
-- title:
--   Unfolding norm-one fibres onto the unit fibre
-- statement:
--   Setting. $K \subseteq L$ are number fields with $L/K$ Galois, $\sigma \in \mathrm{Gal}(L/K)$ is an element such that every $\tau \in \mathrm{Gal}(L/K)$ lies in `Subgroup.zpowers σ` (hypothesis `hgen`; so the group is cyclic with generator $\sigma$), and `D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L` is a descent datum, i.e. a monoid homomorphism `D.act` from $\mathrm{Gal}(L/K)$ to the ring automorphisms of the adele ring $\mathbb{A}_L$ which is compatible with $\mathrm{algebraMap}$ on $L$-rational points and continuous for each group element.
--
--   On the idele group $\mathbb{A}_L^{\times}$ a measurable space together with the assumption that it is the Borel structure are fixed, $\nu_{ZL}$ is a Haar measure on $\mathbb{A}_L^{\times}$, and $\Omega_L$ is a set with hypothesis `hΩL`: $\Omega_L$ is a fundamental domain for the subgroup of principal ideles, the range of `Units.map (algebraMap L (AdeleRing (𝓞 L) L))`, with respect to $\nu_{ZL}$. Further, `ξL` is a monoid homomorphism from the top subgroup of $\mathbb{A}_L^{\times}$ to $\mathbb{C}^{\times}$ such that $z \mapsto \xi_L(z) \in \mathbb{C}$ is continuous (`hξc`) and $\xi_L$ is trivial on the principal ideles (`hξt`); $\varphi : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ is continuous (`hφc`) with compact support (`hφs`); and $R \in \mathbb{R}$ is a truncation parameter.
--
--   Three fundamental-domain hypotheses are imposed, all taken with respect to the Borel $\sigma$-algebras [`NumberField.AdelicHaar.adeleBorel`](def/NumberField_AdelicHaar.html#L132) on $\mathbb{A}_L$ and [`NumberField.Idele.ideleBorel`](def/NumberField_IdeleProductMeasure.html#L384) on $\mathbb{A}_L^{\times}$: `hX` says that $X \subseteq \mathbb{A}_L$ is an additive fundamental domain for the principal subgroup $L \subseteq \mathbb{A}_L$ with respect to `adelicAddHaar (𝓞 L) L`; `hΩ₂` says that $\Omega_2 \subseteq \mathbb{A}_L^{\times}$ is a fundamental domain for the principal ideles $L^{\times}$ with respect to [`NumberField.Idele.idelicHaar L`](def/NumberField_IdeleProductMeasure.html#L391); and `hΩ₂Km`, `hΩ₂K` say that $\Omega_2^K \subseteq \mathbb{A}_L^{\times}$ is measurable and is a fundamental domain, for the same measure, for the range of the homomorphism obtained by composing `Units.map (algebraMap K (AdeleRing (𝓞 K) K))` with [`AutomorphicForm.TransversalMeasure.idelesBaseChange K L`](def/AutomorphicForm_TransversalMeasure.html#L85), the latter being `Units.map` of the ring map [`M4aHerbrand.Bridge.genuineβ K L`](def/M4aHerbrand_GenuineBeta.html#L14); that is, for the image of $K^{\times}$ in $\mathbb{A}_L^{\times}$.
--
--   The integrands. For $x \in \mathbb{A}_L$, $t \in \mathbb{A}_L^{\times}$ and $k$ in `adelicMaximalCompact L` (the subgroup of $\mathrm{GL}_2(\mathbb{A}_L)$ whose finite part lies in `finiteIntegralGL2` and whose archimedean component at each infinite place is a row isometry) write $g = n(x)\,\mathrm{diag}(t,1)\,k$, where $n(x) = \begin{pmatrix}1 & x\\ 0 & 1\end{pmatrix}$ is `unipotentGL2 x` and $\mathrm{diag}(t,1)$ is `diagOne t`. For $\zeta \in \mathbb{A}_L^{\times}$ and $a \in L^{\times}$ with $\mathrm{Norm}_{L/K}(a) = 1$, the first term is the finite sum
--   $$A_a = \sum_{\delta}^{\mathrm{f}} \varphi\bigl(g^{-1} \cdot \mathrm{globalPoints}(\delta) \cdot (\mathrm{sigmaAdelicAct}\,\sigma)(\zeta \cdot g)\bigr),$$
--   the `finsum` being over those $\delta \in \mathrm{GL}_2(L)$ which lie in `TwistedBruhat.normUnipotentSet K L σ hgen` — that is, for which there exists $\gamma \in \mathrm{GL}_2(K)$ of unipotent type (`unipotentCell K`) whose conjugacy class equals the image under [`LT.TwistedNorm.normClassMap hgen`](def/TwistedNormClasses.html#L766) of the $\sigma$-conjugacy class of $\delta$ — and satisfy $\delta_{10} = 0$, $\delta_{11} = 1$, $\delta_{00} = a$. Here `globalPoints` is the entrywise map $\mathrm{GL}_2(L) \to \mathrm{GL}_2(\mathbb{A}_L)$, `sigmaAdelicAct K L D σ` is the entrywise map induced by the ring automorphism `D.act σ`, and $\zeta \cdot g$ abbreviates `centralScalar (𝓞 L) L ζ * g`, multiplication by the central scalar matrix $\zeta$.
--
--   The second term is the truncation
--   $$T_a = \mathbf{1}_{\{h \,:\, \mathrm{adelicHeight}_L(h) > e^{R}\}}(\zeta \cdot g)\; \int \Bigl(\sum_{\delta}^{\mathrm{f}} \varphi\bigl(g^{-1} \cdot \mathrm{globalPoints}(\delta) \cdot (\mathrm{sigmaAdelicAct}\,\sigma)(n(q)\cdot \zeta \cdot g)\bigr)\Bigr)\, d\mu(q),$$
--   where the indicator is `Set.indicator` of [`AutomorphicForm.highSet (adelicHeight L) (Real.exp R)`](def/AutomorphicForm_TruncationOperator.html#L36), the inner `finsum` is over the $\delta \in \mathrm{GL}_2(L)$ with $\delta_{10} = 0$, $\delta_{11} = 1$, $\delta_{00} = a$ only (the membership in `normUnipotentSet` is not imposed in the constant term), and $\mu$ is the probability measure obtained by conditioning `adelicAddHaar (𝓞 L) L` on the box `adelicBox L`; the outer matrix $g$ occurring inside $\varphi$ is the same $g$ as above, while the point of evaluation of the constant term is $\zeta \cdot g$. Finally $|t| =$ [`NumberField.TateGlobal.ideleNorm L t`](def/NumberField_TateGlobalZeta.html#L19) is the modulus by which $t$ scales the additive Haar measure of $\mathbb{A}_L$.
--
--   Hypothesis `hfin` requires finiteness of the absolute iterated lower integral over the $L^{\times}$-domain:
--   $$\int^{-}_{x \in X} \int^{-}_{t \in \Omega_2} \int^{-}_{k} \Bigl(\int^{-}_{\zeta} \lVert \xi_L(\zeta)\rVert_{e} \sum_{a}' \lVert A_a - T_a \rVert_{e}\, d\nu_{ZL}\Bigr)\, \mathrm{ofReal}\,|t|^{-1} \ne \top,$$
--   the sum being over the $a \in L^{\times}$ of norm $1$, and the measures being `maximalCompactHaar L` in $k$ (unrestricted), `idelicHaar L` in $t$ and `adelicAddHaar (𝓞 L) L` in $x$.
--
--   Conclusion. The assertion is a conjunction of two statements.
--
--   First, an equality of Bochner integrals: the iterated integral
--   $$\int_{x \in X} \int_{t \in \Omega_2} \int_{k} \Bigl(\int_{\zeta} \xi_L(\zeta) \sum_{a}' (A_a - T_a)\, d\nu_{ZL}\Bigr)\, |t|^{-1}$$
--   equals the same expression with $\Omega_2$ replaced by $\Omega_2^K$ and with the sum over the norm-one $a$ replaced by its single term at $a = 1$, i.e. with $A_1 - T_1$, where in both the `normUnipotentSet`-constrained sum and in the constant-term sum the condition $\delta_{00} = a$ is replaced by $\delta_{00} = 1$; all measures, the inner $\zeta$-integral against $\nu_{ZL}$, the $k$-integral against `maximalCompactHaar L`, the $t$-integral against `idelicHaar L` and the $x$-integral against `adelicAddHaar (𝓞 L) L`, are as above, and the factor $|t|^{-1}$ is taken as a complex number.
--
--   Secondly, the corresponding unit-fibre lower integral is finite:
--   $$\int^{-}_{x \in X} \int^{-}_{t \in \Omega_2^K} \int^{-}_{k} \Bigl(\int^{-}_{\zeta} \lVert \xi_L(\zeta)\rVert_{e}\, \lVert A_1 - T_1 \rVert_{e}\, d\nu_{ZL}\Bigr)\, \mathrm{ofReal}\,|t|^{-1} \ne \top,$$
--   with the same conventions, $A_1$ and $T_1$ being the $a = 1$ terms described above.
--
--   This is the unfolding step in the comparison of twisted orbital integrals for $\mathrm{GL}_2$ over a cyclic extension $L/K$: by Hilbert 90 a norm-one element of $L^{\times}$ is of the form $e/\sigma(e)$ with $e$ unique modulo $K^{\times}$, so the sum over the norm-one fibres against a fundamental domain for $L^{\times}$ collapses to the single unit fibre $a = 1$ against a fundamental domain for $K^{\times}$, the finiteness of the absolute integral being transported along with the equality. It is used by [`AutomorphicForm.TwistedBruhat.lintegral_ne_top_and_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_mul_integral_finsum_tracePushforward_sub`](thm.html#AutomorphicForm.TwistedBruhat.lintegral_ne_top_and_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_mul_integral_finsum_tracePushforward_sub) in the evaluation of the twisted cuspidal kernel minus its truncation in Iwasawa coordinates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_TwistedBruhat_integral_iwasawa_tsum_normOneFibre_eq_integral_unitFibre_of_fibrewise.lean

import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Definitions.Def_AutomorphicForm_TransversalMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm AutomorphicForm.AdelicTracePushforward
open scoped TensorProduct Pointwise ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.TwistedBruhat.integral_iwasawa_tsum_normOneFibre_eq_integral_unitFibre_of_fibrewise
    (K L : Type)
    [Field K]
    [NumberField K]
    [Field L]
    [NumberField L]
    [Algebra K L]
    [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ]
    [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (hφc : Continuous φ)
    (hφs : HasCompactSupport φ)
    (R : ℝ)
    (X : Set (AdeleRing (𝓞 L) L))
    (Ω₂ : Set (AdeleRing (𝓞 L) L)ˣ)
    (Ω₂K : Set (AdeleRing (𝓞 L) L)ˣ)
    (hX : @IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) _ _ _
      (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) X (adelicAddHaar (𝓞 L) L))
    (hΩ₂ : @IsFundamentalDomain (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range _ _ _
      (NumberField.Idele.ideleBorel L) Ω₂ (NumberField.Idele.idelicHaar L))
    (hΩ₂Km : @MeasurableSet _ (NumberField.Idele.ideleBorel L) Ω₂K)
    (hΩ₂K : @IsFundamentalDomain
      ((AutomorphicForm.TransversalMeasure.idelesBaseChange K L).comp
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K))).range _ _ _
      (NumberField.Idele.ideleBorel L) Ω₂K (NumberField.Idele.idelicHaar L))
    (hfin : ∫⁻ x in X, ∫⁻ t in Ω₂, ∫⁻ k,
            (∫⁻ ζ, ‖((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ)‖ₑ *
                ∑' a : {α : Lˣ // Algebra.norm K (α : L) = 1},
              ‖(∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = ((a : Lˣ) : L)},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = ((a : Lˣ) : L)},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)))‖ₑ ∂νZL) *
              ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) ≠ ⊤) :
    (∫ x in X, ∫ t in Ω₂, ∫ k,
            (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
                ∑' a : {α : Lˣ // Algebra.norm K (α : L) = 1},
              ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = ((a : Lˣ) : L)},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = ((a : Lˣ) : L)},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)))) ∂νZL) *
              (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) =
      ∫ x in X, ∫ t in Ω₂K, ∫ k,
            (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
              ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)))) ∂νZL) *
              (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L)) ∧
    (∫⁻ x in X, ∫⁻ t in Ω₂K, ∫⁻ k,
            (∫⁻ ζ, ‖((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ)‖ₑ *
              ‖(∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)))‖ₑ ∂νZL) *
              ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) ≠ ⊤) := by sorry
