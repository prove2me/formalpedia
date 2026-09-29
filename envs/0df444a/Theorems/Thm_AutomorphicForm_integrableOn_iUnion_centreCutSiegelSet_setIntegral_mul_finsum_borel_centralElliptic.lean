-- Prove2me | Theorems.Thm_AutomorphicForm_integrableOn_iUnion_centreCutSiegelSet_setIntegral_mul_finsum_borel_centralElliptic
-- name    : AutomorphicForm.integrableOn_iUnion_centreCutSiegelSet_setIntegral_mul_finsum_borel_centralElliptic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/71d258ff-a11c-5867-a294-c3c46e03ab2d
-- title:
--   Integrability of the central–elliptic twisted kernel over centre-cut Siegel translates
-- statement:
--   Let $L/K$ be a Galois extension of number fields, $\nu_{Z_L}$ a Haar measure on the idele group $(\mathbb{A}_L)^\times$ (for a Borel measurable structure on it), and $\Omega_L$ a fundamental domain for the subgroup of principal ideles, the range of $L^\times\to(\mathbb{A}_L)^\times$, with respect to $\nu_{Z_L}$. Let $D$ be an `IdeleGaloisDescent` datum, i.e. a homomorphism from $\mathrm{Gal}(L/K)$ to ring automorphisms of $\mathbb{A}_L$ that is continuous and extends the action on $L$; let $\sigma\in\mathrm{Gal}(L/K)$ be such that every $\tau$ lies in the subgroup of integral powers of $\sigma$; let $\xi_L$ be a homomorphism from the full idele group to $\mathbb{C}^\times$, continuous as a $\mathbb{C}$-valued function and trivial on principal ideles. Fix a finite set $S$ of primes of $\mathcal{O}_K$, functions $\varphi_a$ on $\mathrm{GL}_2$ of the infinite adeles of $L$ and $\varphi_{S,v}$ on $\mathrm{GL}_2(L\otimes_K K_v)$, reals $c,u,d_1,d_2$ with $c>0$, $d_1>0$, and a finite set $\mathtt{tset}\subseteq\mathrm{GL}_2(\mathbb{A}_L)$. The assertion is: for every finite set $T$ of primes of $\mathcal{O}_K$, every choice for each prime $v$ of $\mathcal{O}_K$ of an extension $w_v$ of $v$ to $\mathcal{O}_L$, of $n_v\in\mathbb{N}$, of elements $r_{v,0},\dots,r_{v,n_v-1}$ and $z_v$ of $\mathrm{GL}_2(L_{w_v})$, of exponents $k_v,j_v\in\mathbb{N}$, and every pair of functions $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_L)$ and $\varphi_f$ on $\mathrm{GL}_2$ of the finite adeles, if $\varphi,\varphi_a,\varphi_f$ and the family sending $v\in T$ to $x\mapsto\sum_{\iota:\mathrm{Fin}(k_v)\to\mathrm{Fin}(n_v)}\mathbf{1}_{\mathcal{K}_v}\big(\mathrm{sc}_v(\prod_m r_{v,\iota(m)}\cdot z_v^{\,j_v})^{-1}x\big)$, where $\mathcal{K}_v$ is the set of semi-local matrices integral together with their inverses, $\mathrm{sc}_v$ is the semi-local component map and the local element is embedded in the finite adelic group at $w_v$, and $v\notin T$ to $\varphi_{S,v}$, form a semi-local factorisation for $S\cup T$ (i.e. $\varphi_a$ is smooth in the matrix entries with compact support, $\varphi_f$ is locally constant with compact support, each factor at $v\in S\cup T$ is locally constant with compact support, $\varphi_f(h)$ equals the product of these factors on the semi-local components of $h$ whenever all components outside $S\cup T$ are integral and vanishes otherwise, and $\varphi(g)=\varphi_a(g_\infty)\varphi_f(g_f)$), then: first, for every $x\in\mathrm{GL}_2(\mathbb{A}_L)$ the function $z\mapsto\xi_L(z)\sum_\delta\varphi\big(x^{-1}\,\delta\,\sigma_{\mathbb{A}}(\mathrm{diag}(z,z)\,x)\big)$ is integrable on $\Omega_L$ against $\nu_{Z_L}$, the sum running over those $\delta\in\mathrm{GL}_2(L)$, viewed in $\mathrm{GL}_2(\mathbb{A}_L)$, with vanishing lower-left entry whose $\sigma$-conjugacy class has norm class equal to the conjugacy class of some $\gamma\in\mathrm{GL}_2(K)$ that is either elliptic (its characteristic polynomial has no root in $K$) or central (a scalar matrix), and $\sigma_{\mathbb{A}}$ denoting the action of $\sigma$ on $\mathrm{GL}_2(\mathbb{A}_L)$ through $D$; and second, the function $x\mapsto\int_{\Omega_L}$ of that same integrand is integrable, against the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_L)$, over the union of the right translates by $y\in\mathtt{tset}$ of the centre-cut Siegel set of parameters $(c,u,d_1,d_2)$, namely the $g$ with integral finite part and whose archimedean component satisfies, at every infinite place $w$ of $L$, local height at least $c$, window coordinate at most $u^2$, and determinant norm in $[d_1,d_2]$.
--
--   This is an integrability input for the geometric side of the twisted trace formula for $\mathrm{GL}_2$ over a cyclic extension, isolating the contribution of the upper-triangular $\delta$ whose norm class is central or elliptic, weighted by an idele class character. It is used in [`AutomorphicForm.integrableOn_setIntegral_mul_finsum_centralElliptic_twistedAdelicKernel`](thm.html#AutomorphicForm.integrableOn_setIntegral_mul_finsum_centralElliptic_twistedAdelicKernel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrableOn_iUnion_centreCutSiegelSet_setIntegral_mul_finsum_borel_centralElliptic.lean

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

theorem AutomorphicForm.integrableOn_iUnion_centreCutSiegelSet_setIntegral_mul_finsum_borel_centralElliptic
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))] [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ]
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
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (hd₁ : 0 < d₁) (tset : Finset (AdelicGL2 (𝓞 L) L)) :
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
        (∑ᶠ δ ∈ {δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ ∃ γ : GL (Fin 2) K,
            (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)))) ΩL νZL) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (∑ᶠ δ ∈ {δ : GL (Fin 2) L | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ ∃ γ : GL (Fin 2) K,
            (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZL))
        (⋃ y ∈ tset, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
        (adelicGLHaar (Fin 2) (𝓞 L) L) := by sorry
