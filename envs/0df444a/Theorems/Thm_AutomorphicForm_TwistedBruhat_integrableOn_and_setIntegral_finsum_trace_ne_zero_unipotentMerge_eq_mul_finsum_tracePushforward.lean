-- Prove2me | Theorems.Thm_AutomorphicForm_TwistedBruhat_integrableOn_and_setIntegral_finsum_trace_ne_zero_unipotentMerge_eq_mul_finsum_tracePushforward
-- name    : AutomorphicForm.TwistedBruhat.integrableOn_and_setIntegral_finsum_trace_ne_zero_unipotentMerge_eq_mul_finsum_tracePushforward
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/1b1be0b7-4dad-5206-9bc7-6687406d3798
-- title:
--   Unipotent merge: fundamental-domain integral as trace push-forward sum
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois, let $D$ be an idele Galois descent datum for $L/K$ (a homomorphism $\mathrm{Gal}(L/K) \to \mathrm{Aut}_{\mathrm{ring}}(\mathbb A_L)$ whose automorphisms are continuous and extend the action on $L$ through $L \to \mathbb A_L$), and let $\sigma \in \mathrm{Gal}(L/K)$ be such that every $\tau$ lies in the subgroup of integer powers of $\sigma$. Let $\varphi : \mathrm{GL}_2(\mathbb A_L) \to \mathbb C$ be continuous with compact support, let $X \subseteq \mathbb A_L$ be an additive fundamental domain for the principal subgroup $L \subseteq \mathbb A_L$ with respect to the adelic Haar measure $\mu_L$, and let $\mu_K$ be an additive Haar measure on $\mathbb A_K$, for a Borel measurable structure, with $\mu_K$ of the adelic box (infinite box times integral finite adeles) equal to $1$. Let $c \in [0,\infty]$ with $c \neq 0, \infty$ satisfy the disintegration identity $\int^- G \, d\mu_L = c \int^-_r \int^-_w G(\mathrm{traceFibre}_{K,L}(r,w)) \, dw \, d\mu_K(r)$ for all measurable $G : \mathbb A_L \to [0,\infty]$, where $w$ ranges over the product measure on $\mathrm{Fin}(\dim_K \ker \mathrm{Tr}_{L/K})$ copies of $\mathbb A_K$ and $\mathrm{traceFibre}$ is the explicit section $r \cdot (\dim_K L)^{-1} + \sum_i w_i \cdot e_i$ built from the chosen base-change embedding $\mathbb A_K \to \mathbb A_L$ and a basis $(e_i)$ of the trace-zero subspace. Finally fix ideles $t, \zeta \in \mathbb A_L^\times$ and $k$ in the adelic maximal compact subgroup of $\mathrm{GL}_2(\mathbb A_L)$ (finite part integral, archimedean components row isometries). Put $$G(w) = \varphi\bigl(k^{-1}\, n(w t^{-1})\, d(\sigma_D(t) t^{-1})\, z(\sigma_D(\zeta))\, \sigma_D(k)\bigr),$$ where $n(y) = \begin{pmatrix} 1 & y \\ 0 & 1\end{pmatrix}$, $d(a) = \mathrm{diag}(a,1)$, $z(a)$ is the central scalar matrix, $\sigma_D$ denotes the action of $\sigma$ through $D$ on ideles and entrywise on matrices. Then the function $x \mapsto \sum_{b} G(b + \sigma_D(x) - x)$, the unconditional sum over $\{b \in L : \mathrm{Tr}_{L/K}(b) \neq 0\}$, is integrable on $X$ with respect to $\mu_L$, and $$\int_X \sum_{b} G(b + \sigma_D(x) - x) \, d\mu_L(x) = c \sum_{\eta \in K^\times} \bigl(\textstyle\int G(\mathrm{traceFibre}_{K,L}(\eta, w)) \, dw\bigr),$$ the right-hand sum being over $\eta \in K^\times$, embedded into $\mathbb A_K$, of the trace push-forward of $G$, and $c$ entering as its real part cast to $\mathbb C$.
--
--   This is the unipotent merge step (additive Hilbert 90 together with surjectivity of $\mathrm{Tr}_{L/K}$) in the computation of the unipotent contribution to a base-change trace identity for $\mathrm{GL}_2$: the sum over $b \in L$ with nonzero trace of translates of a coboundary $\sigma_D(x) - x$, integrated over a fundamental domain for $L$ in $\mathbb A_L$, is converted into a sum over $K^\times$ of trace push-forwards to $\mathbb A_K$. It is used in [`AutomorphicForm.TwistedBruhat.lintegral_ne_top_and_integral_iwasawa_unitFibre_eq_mul_integral_finsum_tracePushforward_sub`](thm.html#AutomorphicForm.TwistedBruhat.lintegral_ne_top_and_integral_iwasawa_unitFibre_eq_mul_integral_finsum_tracePushforward_sub).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_TwistedBruhat_integrableOn_and_setIntegral_finsum_trace_ne_zero_unipotentMerge_eq_mul_finsum_tracePushforward.lean

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

theorem AutomorphicForm.TwistedBruhat.integrableOn_and_setIntegral_finsum_trace_ne_zero_unipotentMerge_eq_mul_finsum_tracePushforward
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
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
        ∑ᶠ b ∈ {b : L | Algebra.trace K L b ≠ 0},
          φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
            unipotentGL2 ((algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x) * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
            diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
            centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
            AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)))
      X (adelicAddHaar (𝓞 L) L) ∧
    (∫ x in X, ∑ᶠ b ∈ {b : L | Algebra.trace K L b ≠ 0},
          φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
            unipotentGL2 ((algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x) * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
            diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
            centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
            AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))
        ∂(adelicAddHaar (𝓞 L) L)) =
      (c.toReal : ℂ) * ∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K)) := by sorry
