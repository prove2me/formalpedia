-- Prove2me | Theorems.Thm_AutomorphicForm_integrableOn_setIntegral_mul_finsum_centralElliptic_twistedAdelicKernel
-- name    : AutomorphicForm.integrableOn_setIntegral_mul_finsum_centralElliptic_twistedAdelicKernel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/7404a682-2a32-5513-90d3-9840c196291b
-- title:
--   Integrability of the central–elliptic twisted kernel against an idele character
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois, let $\alpha,\beta \in \mathbb{R}$ with $0 < \alpha < \beta$, let $\nu_{Z_L}$ be a Haar measure on the idele group $(\mathbb{A}_L)^\times$ (for a Borel measurable structure on it) and let $\Omega_L$ be a fundamental domain for the translation action of the image of $L^\times$ in $(\mathbb{A}_L)^\times$ with respect to $\nu_{Z_L}$. Let $D$ be a Galois descent datum for the adeles of $L$ over $K$, i.e. a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$ which is continuous in each $\tau$ and compatible with the action on $L$ through $L \to \mathbb{A}_L$; let $\sigma \in \mathrm{Gal}(L/K)$ be such that every $\tau$ lies in the subgroup of integer powers of $\sigma$; and let $\xi_L$ be a homomorphism from the full idele group of $L$ to $\mathbb{C}^\times$ which is continuous as a $\mathbb{C}$-valued function and trivial on the principal ideles. Let $S$ be a finite set of primes of $\mathcal{O}_K$, let $\varphi_a$ be a function on $\mathrm{GL}_2$ of the infinite adeles of $L$, let $\varphi_S$ assign to each prime $v$ of $\mathcal{O}_K$ a function on $\mathrm{GL}_2(L \otimes_K K_v)$, and let $\Phi_0 \subseteq \mathrm{GL}_2(\mathbb{A}_L)$ be contained in $\{g : \lVert \det g \rVert \in [\alpha,\beta]\}$ (idelic norm, defined through the scaling of Haar measure) and be a fundamental domain for the image of $\mathrm{GL}_2(L)$ acting on the left with respect to the Haar measure of $\mathrm{GL}_2(\mathbb{A}_L)$ restricted to that determinant slab. Then for every finite set $T$ of primes of $\mathcal{O}_K$, every choice at each $v$ of an extension $w_v$ of $v$ to $\mathcal{O}_L$, of $n_v \in \mathbb{N}$, of elements $r_{v,0},\dots,r_{v,n_v-1}$ and $z_v$ of $\mathrm{GL}_2(L_{w_v})$ and of exponents $k_v, j_v \in \mathbb{N}$, and for all $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_L)$ and $\varphi_f$ on $\mathrm{GL}_2$ of the finite adeles of $L$: if $\varphi$ factorises semi-locally over $S \cup T$ as $\varphi_a$ times $\varphi_f$ with semi-local factors given at $v \in T$ by $x \mapsto \sum_{\iota : \mathrm{Fin}(k_v) \to \mathrm{Fin}(n_v)} \mathbf{1}_{\text{integral set at } v}\big( (\text{semi-local component at } v \text{ of the local embedding of } \prod_m r_{v,\iota(m)} \cdot z_v^{\,j_v})^{-1} x \big)$ and at $v \notin T$ by $\varphi_S(v)$ — that is, $\varphi_a$ is smooth of compact support in mixed-space coordinates, $\varphi_f$ is locally constant of compact support, each semi-local factor at a place of $S\cup T$ is locally constant of compact support, $\varphi_f(h)$ equals the product of the semi-local factors at $S \cup T$ when $h$ is integral at all $v \notin S \cup T$ and vanishes otherwise, and $\varphi(g) = \varphi_a(g_\infty)\varphi_f(g_f)$ — then (i) for every $x \in \mathrm{GL}_2(\mathbb{A}_L)$ the function $$z \mapsto \xi_L(z) \sum_{\delta} \varphi\big(x^{-1}\, \delta\, \sigma_{\mathbb{A}}(\mathrm{diag}(z,z)\,x)\big),$$ the finite sum running over those $\delta \in \mathrm{GL}_2(L)$ whose $\sigma$-conjugacy class has norm class equal to the conjugacy class of some $\gamma \in \mathrm{GL}_2(K)$ which is either elliptic (its characteristic polynomial has no root in $K$) or central (a scalar matrix), with $\delta$ mapped into $\mathrm{GL}_2(\mathbb{A}_L)$ and $\sigma_{\mathbb{A}}$ the action of $\sigma$ through $D$, is integrable on $\Omega_L$ with respect to $\nu_{Z_L}$; and (ii) the function sending $x$ to the integral of that expression over $\Omega_L$ against $\nu_{Z_L}$ is integrable on $\Phi_0$ with respect to the Haar measure of $\mathrm{GL}_2(\mathbb{A}_L)$.
--
--   This is the convergence input for the central and elliptic contributions to the $\sigma$-twisted kernel on $\mathrm{GL}_2$ over a cyclic extension $L/K$, folded against an idele class character: both the inner integral over the idele class fundamental domain and the resulting function on the quotient by $\mathrm{GL}_2(L)$ are absolutely integrable. It is used in the evaluation of the twisted trace of a Hecke-type test function, where the geometric side is split into its central–elliptic part and a remainder with controlled norm.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrableOn_setIntegral_mul_finsum_centralElliptic_twistedAdelicKernel.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel
open scoped TensorProduct.RightActions in

theorem AutomorphicForm.integrableOn_setIntegral_mul_finsum_centralElliptic_twistedAdelicKernel
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ]
    [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure]
    (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K)))
      (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
      (ns : HeightOneSpectrum (𝓞 K) → ℕ)
      (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L))
      (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
      (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
      (φ : AdelicGL2 (𝓞 L) L → ℂ)
      (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
      (∀ x : AdelicGL2 (𝓞 L) L, IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ =>
        ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)))) ΩL νZL) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZL))
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) := by sorry
