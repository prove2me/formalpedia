-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_abs_log_adelicHeight_mul_adelicHeight_adelicWeyl_le_mul_prod_pow_log_measure_of_doubleCoset_apply_ne_zero
-- name    : AutomorphicForm.exists_forall_abs_log_adelicHeight_mul_adelicHeight_adelicWeyl_le_mul_prod_pow_log_measure_of_doubleCoset_apply_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/438f92fd-30bf-590b-9e63-ee09e3a9f4eb
-- title:
--   Height weight bounded on the support of twisted double-coset integrands
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois, let $D$ be an idèle Galois descent datum for $\mathcal{O}_L/K/L$ (a homomorphism from $\mathrm{Gal}(L/K)$ to ring automorphisms of $\mathbb{A}_L$, compatible with the structure map from $L$ and continuous), let $\sigma \in \mathrm{Gal}(L/K)$ be such that every $\tau$ lies in the subgroup of integer powers of $\sigma$, let $S$ be a finite set of height-one primes of $\mathcal{O}_K$, let $\varphi_a$ be a function on $\mathrm{GL}_2$ of the infinite adèle ring of $L$ and $\varphi_S$ a family of functions on $\mathrm{GL}_2(L \otimes_K K_v)$. Then for every finite set $T$ of height-one primes of $\mathcal{O}_K$ and every choice $w_v$ of a height-one prime of $\mathcal{O}_L$ lying under $v$, there are a real $C \ge 0$ and a natural number $A$ with the following property. Let $\rho$ assign to each $v$ an element of $\mathrm{GL}_2$ of the completion of $L$ at $w_v$, and let $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_L)$ and $\varphi_f$ on $\mathrm{GL}_2$ of the finite adèle ring satisfy `IsSemiLocalFactorization` for the set $S \cup T$ with archimedean factor $\varphi_a$, finite factor $\varphi_f$, and semi-local factors given at $v \in T$ by the indicator function, with value $1$, of the double coset $\mathcal{K}_v \cdot \{\mathrm{semiLocalComponent}\,(\rho_v)\} \cdot \mathcal{K}_v$, where $\mathcal{K}_v =$ `semiLocalIntegralSet K L v` is the integral units set of the semi-local integers and $\rho_v$ is first embedded into $\mathrm{GL}_2$ of the finite adèles by [`AdelicDock.localEmbed`](def/AdelicDock_LocalEmbedding.html#L97), and at $v \notin T$ by $\varphi_S(v)$; that is, $\varphi_a$ is an arch test factor, $\varphi_f$ a finite test factor, each semi-local factor at $v \in S \cup T$ is a semi-local test function, $\varphi_f(h)$ equals the product over $v \in S \cup T$ of the semi-local factors evaluated at the semi-local components of $h$ whenever all components outside $S \cup T$ are integral and vanishes otherwise, and $\varphi(g) = \varphi_a(g_\infty)\varphi_f(g_f)$. Then for every $t \in \mathrm{GL}_2(L)$ with vanishing $(1,0)$ and $(0,1)$ entries and with $N_{K}(t_{00}/t_{11}) \ne 1$, and all $y \in \mathrm{GL}_2(\mathbb{A}_L)$ and $z \in \mathbb{A}_L^\times$, non-vanishing of $\varphi\bigl(y^{-1} \cdot t \cdot \sigma_D(z \cdot y)\bigr)$, where $t$ and $z$ act through the global-points and central-scalar maps and $\sigma_D$ is the automorphism of $\mathrm{GL}_2(\mathbb{A}_L)$ induced by $D(\sigma)$, implies $$\bigl|-\log H(y) - \log H(\mathrm{w}\,y)\bigr| \le C \prod_{v \in T} \bigl(1 + \log \mu_v(\mathcal{K}_v \rho_v \mathcal{K}_v)\bigr)^A,$$ where $H$ is the adèlic height (product of the archimedean and finite heights of the two components), $\mathrm{w}$ is the adèlic Weyl element (the global point attached to `gl2Weyl`), and $\mu_v$ is the semi-local Haar measure on $\mathrm{GL}_2(L \otimes_K K_v)$ normalised on the integral compacts, its value taken as a real number.
--
--   This is the support-excursion estimate for the weighted hyperbolic class term: on the support of a twisted orbital integrand built from Hecke double-coset test functions at the places of $T$, the height weight comparing $y$ with $\mathrm{w}y$ is bounded by a fixed power of the logarithm of the double-coset volumes. It is used in the bound for the integral of the weighted twisted orbital expression against the corresponding unweighted orbital integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_abs_log_adelicHeight_mul_adelicHeight_adelicWeyl_le_mul_prod_pow_log_measure_of_doubleCoset_apply_ne_zero.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_forall_abs_log_adelicHeight_mul_adelicHeight_adelicWeyl_le_mul_prod_pow_log_measure_of_doubleCoset_apply_ne_zero
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))) (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L)),
      ∃ C : ℝ, 0 ≤ C ∧ ∃ A : ℕ,
      ∀ (ρ : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                  semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) x
            else φS v) →
      ∀ (t : GL (Fin 2) L), (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 → (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 →
        Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1 →
      ∀ (y : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ),
        φ (y⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * y)) ≠ 0 →
        |(-Real.log (NumberField.AdelicHeight.adelicHeight L y)
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * y)))| ≤
        C * ∏ v ∈ T,
          ((1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal) ^ A) := by sorry
