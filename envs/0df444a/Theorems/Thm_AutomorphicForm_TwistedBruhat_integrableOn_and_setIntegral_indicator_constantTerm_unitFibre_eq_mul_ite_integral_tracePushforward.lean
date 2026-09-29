-- Prove2me | Theorems.Thm_AutomorphicForm_TwistedBruhat_integrableOn_and_setIntegral_indicator_constantTerm_unitFibre_eq_mul_ite_integral_tracePushforward
-- name    : AutomorphicForm.TwistedBruhat.integrableOn_and_setIntegral_indicator_constantTerm_unitFibre_eq_mul_ite_integral_tracePushforward
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/e340489c-d061-5af7-8edf-a8620c54899b
-- title:
--   Truncated twisted constant term integrated over a fundamental domain
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois, let $D$ be an idèle-theoretic Galois descent datum for $L/K$ (a homomorphism from $\mathrm{Gal}(L/K)$ to ring automorphisms of $\mathbb{A}_L$, compatible with $\mathrm{Gal}(L/K)$ acting on $L$ via $L \to \mathbb{A}_L$ and continuous in each automorphism), and let $\sigma \in \mathrm{Gal}(L/K)$. Let $\varphi : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ be continuous with compact support, $R \in \mathbb{R}$, and $X \subseteq \mathbb{A}_L$ an additive fundamental domain for the principal subgroup $L \subseteq \mathbb{A}_L$ with respect to the Haar measure $\mu_L =$ `adelicAddHaar`. Let $\mu_K$ be an additive Haar measure on $\mathbb{A}_K$, taken with the Borel $\sigma$-algebra, normalised by $\mu_K(\mathrm{adelicBox}\, K) = 1$, and let $c \in [0,\infty]$ be non-zero and finite such that for every measurable $G : \mathbb{A}_L \to [0,\infty]$ one has $\int^- G \, d\mu_L = c \int^-_{r} \int^-_{w} G(\mathrm{traceFibre}_{K,L}(r,w)) \, d\mu_K^{\otimes d}(w) \, d\mu_K(r)$, where $d = \dim_K \ker(\mathrm{Tr}_{L/K})$ and $\mathrm{traceFibre}$ is the parametrisation of $\mathbb{A}_L$ by $\mathbb{A}_K \times \mathbb{A}_K^d$ given by the $\beta$-bridge applied to $r/[L:K]$ plus the combination of a chosen basis of the trace kernel. Finally let $t, \zeta \in \mathbb{A}_L^\times$ and let $k$ lie in the maximal compact subgroup of $\mathrm{GL}_2(\mathbb{A}_L)$ consisting of elements whose finite part is integral of level $\top$ and each of whose archimedean components is a row isometry. Write $g_x = n(x)\,d(t)\,k$, where $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $d(t) = \mathrm{diag}(t,1)$, and let
--   $$F_x(y) = \sum_{\delta}\varphi\bigl(g_x^{-1}\,\iota(\delta)\,\sigma_D(y)\bigr),$$
--   the finite-support sum over those $\delta \in \mathrm{GL}_2(L)$ with $\delta_{10} = 0$, $\delta_{11} = 1$, $\delta_{00} = 1$, with $\iota$ the map $\mathrm{GL}_2(L) \to \mathrm{GL}_2(\mathbb{A}_L)$ and $\sigma_D$ the automorphism of $\mathrm{GL}_2(\mathbb{A}_L)$ induced by $D(\sigma)$. Let $T(x)$ be the constant term $\int F_x(n(q)\,z(\zeta)\,g_x)\,d\mathbb{P}(q)$, taken against $\mu_L$ conditioned on `adelicBox` $L$, multiplied by the indicator of the condition $e^R < \mathrm{ht}(z(\zeta)\,g_x)$, where $\mathrm{ht}$ is the adèlic height and $z(\zeta)$ the central scalar matrix. The assertion is that $T$ is integrable on $X$ for $\mu_L$ and that
--   $$\int_X T \, d\mu_L = c \cdot \mathbf{1}\{e^R < \mathrm{ht}(d(t))\} \int_{\mathbb{A}_K} \mathrm{tracePushforward}_{K,L}(\Psi)(r)\, d\mu_K(r),$$
--   with $\Psi(w) = \varphi\bigl(k^{-1}\,n(wt^{-1})\,d(\sigma_D(t)t^{-1})\,z(\sigma_D(\zeta))\,\sigma_D(k)\bigr)$ and $\mathrm{tracePushforward}_{K,L}(\Psi)(r) = \int \Psi(\mathrm{traceFibre}_{K,L}(r,w))\,d\mu_K^{\otimes d}(w)$, the $\sigma_D$-images of units being taken through the induced automorphism of $\mathbb{A}_L^\times$.
--
--   This computes the unipotent (constant-term) contribution to the $\sigma$-twisted kernel for $\mathrm{GL}_2$ in Iwasawa coordinates: after truncation at height $e^R$ and averaging over the adèlic box, the integral over a fundamental domain for $L \subseteq \mathbb{A}_L$ collapses to a single trace-pushforward integral over $\mathbb{A}_K$, with the height condition depending only on the diagonal part $d(t)$. It feeds the subsequent merge of the Iwasawa unit-fibre terms, [`AutomorphicForm.TwistedBruhat.lintegral_ne_top_and_integral_iwasawa_unitFibre_eq_mul_integral_finsum_tracePushforward_sub`](thm.html#AutomorphicForm.TwistedBruhat.lintegral_ne_top_and_integral_iwasawa_unitFibre_eq_mul_integral_finsum_tracePushforward_sub).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_TwistedBruhat_integrableOn_and_setIntegral_indicator_constantTerm_unitFibre_eq_mul_ite_integral_tracePushforward.lean

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

theorem AutomorphicForm.TwistedBruhat.integrableOn_and_setIntegral_indicator_constantTerm_unitFibre_eq_mul_ite_integral_tracePushforward
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (R : ℝ)
    (X : Set (AdeleRing (𝓞 L) L))
    (hX : @IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) _ _ _
      (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) X (adelicAddHaar (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 K) K)]
    [BorelSpace (AdeleRing (𝓞 K) K)]
    (μK : Measure (AdeleRing (𝓞 K) K))
    [μK.IsAddHaarMeasure]
    (hμK1 : μK (NumberField.AdelicBox.adelicBox K) = 1)
    (c : ℝ≥0∞)
    (hc0 : c ≠ 0)
    (hcT : c ≠ ⊤)
    (hc : ∀ G : AdeleRing (𝓞 L) L → ℝ≥0∞, @Measurable _ _ (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) _ G →
      ∫⁻ x, G x ∂(adelicAddHaar (𝓞 L) L) =
        c * ∫⁻ r, ∫⁻ w, G (traceFibre K L r w)
          ∂(@Measure.pi (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)))) (fun _ => AdeleRing (𝓞 K) K) _
            (fun _ => NumberField.AdelicHaar.adeleBorel (𝓞 K) K) (fun _ => adelicAddHaar (𝓞 K) K)) ∂μK)
    (t ζ : (AdeleRing (𝓞 L) L)ˣ) (k : ↥(adelicMaximalCompact L)) :
    IntegrableOn (fun x : AdeleRing (𝓞 L) L =>
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
          (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))
      X (adelicAddHaar (𝓞 L) L) ∧
    (∫ x in X,
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
          (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)))
        ∂(adelicAddHaar (𝓞 L) L)) =
      (c.toReal : ℂ) *
        (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne t : AdelicGL2 (𝓞 L) L) then
          ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0) := by sorry
