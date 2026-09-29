-- Prove2me | Theorems.Thm_AutomorphicForm_integral_mul_chiDet_eq_prod_sum_localChar_mul_integral_of_isSemiLocalFactorization
-- name    : AutomorphicForm.integral_mul_chiDet_eq_prod_sum_localChar_mul_integral_of_isSemiLocalFactorization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/d6b76580-4d2d-513b-be0c-f6e897d57280
-- title:
--   Hecke words multiply η∘det integrals by local character sums
-- statement:
--   Let $K\subseteq L$ be number fields, let $S,T$ be finite sets of nonzero primes of $\mathcal O_K$ with $T$ and $S$ disjoint, and for each prime $v$ of $\mathcal O_K$ fix a prime $w_v$ of $\mathcal O_L$ lying under $v$, a natural number $n_v$, elements $r_{v,1},\dots,r_{v,n_v}$ and $z_v$ of $\mathrm{GL}_2(L_{w_v})$, and natural numbers $k_v,j_v$. Let $\varphi_{\mathrm a}$ be a function on $\mathrm{GL}_2$ of the infinite adeles of $L$, let $\varphi_v$ be functions on $\mathrm{GL}_2(L\otimes_K K_v)$, let $\varphi$ be a continuous compactly supported function on $\mathrm{GL}_2(\mathbb A_L)$ and $\varphi_{\mathrm f}$ a function on $\mathrm{GL}_2$ of the finite adeles of $L$. The hypothesis `IsSemiLocalFactorization K L (S ∪ T)` asserts: $\varphi_{\mathrm a}$ is an archimedean test factor (given by a smooth function of the matrix entries in the mixed space, with compact support), $\varphi_{\mathrm f}$ satisfies `IsFinTestFactor`, each semi-local component at a place of $S\cup T$ satisfies `IsSemiLocalTestFn`, $\varphi_{\mathrm f}(h)$ equals the product over $v\in S\cup T$ of these components evaluated at the $v$-semi-local component of $h$ whenever that component lies in `semiLocalIntegralSet` for all $v\notin S\cup T$, $\varphi_{\mathrm f}(h)=0$ when some such component fails to be integral, and $\varphi(g)=\varphi_{\mathrm a}(\mathrm{glArch}\,g)\,\varphi_{\mathrm f}(\mathrm{glFin}\,g)$; here the component taken at $v\in T$ is the Hecke word $x\mapsto\sum_{\iota:\{0,\dots,k_v-1\}\to\{1,\dots,n_v\}}\mathbf 1_{\text{integral}}\big(c_v(x_\iota)^{-1}x\big)$, where $x_\iota$ is the image under [`AdelicDock.localEmbed`](def/AdelicDock_LocalEmbedding.html#L97) at $w_v$ of $r_{v,\iota(0)}\cdots r_{v,\iota(k_v-1)}z_v^{\,j_v}$ and $c_v$ is the $v$-semi-local component map, while at $v\in S$ it is $\varphi_v$. Let $\eta$ be a homomorphism from the ideles $(\mathbb A_L)^\times$ to $\mathbb C^\times$ whose composite with the inclusion $\mathbb C^\times\to\mathbb C$ is continuous. Then, for the Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb A_L)$ with its Borel structure, $\int\varphi(g)\,\eta(\det g)\,dg$ equals $\prod_{v\in T}\sum_{\iota}\eta_{w_v}\big(\det(r_{v,\iota(0)}\cdots r_{v,\iota(k_v-1)}z_v^{\,j_v})\big)$, with $\eta_{w_v}$ the local character [`NumberField.TateGlobal.localChar`](def/NumberField_TateGlobalZeta.html#L31) of $\eta$ at $w_v$, times the integral of $\eta(\det g)$ against the function which is $\varphi_{\mathrm a}(\mathrm{glArch}\,g)\prod_{v\in S}\varphi_v(c_v(\mathrm{glFin}\,g))$ on the set of $g$ whose $v$-semi-local components are integral for every $v\notin S$, and $0$ off that set.
--
--   This records the effect on a one-dimensional representation $\eta\circ\det$ of the Hecke operators attached to words $r_{\iota(0)}\cdots r_{\iota(k-1)}z^{j}$ placed at chosen places $w_v$ of $L$ above the places $v\in T$ of the base field: each such word contributes a sum of values of the local character $\eta_{w_v}\circ\det$, and the word-free semi-local integral at $S$ remains. It is used in [`AutomorphicForm.exists_atomic_forall_integrableOn_and_tendsto_setIntegral_lambdaT_finsum_twistedConvOp_chiDet_mul_chiDet_inv`](thm.html#AutomorphicForm.exists_atomic_forall_integrableOn_and_tendsto_setIntegral_lambdaT_finsum_twistedConvOp_chiDet_mul_chiDet_inv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_mul_chiDet_eq_prod_sum_localChar_mul_integral_of_isSemiLocalFactorization.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open IsDedekindDomain AutomorphicForm
open scoped TensorProduct

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.integral_mul_chiDet_eq_prod_sum_localChar_mul_integral_of_isSemiLocalFactorization
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T S)
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (ns : HeightOneSpectrum (𝓞 K) → ℕ)
    (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L))
    (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
    (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (hfact : IsSemiLocalFactorization K L (S ∪ T) φ φa φf
      (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
        ∑ ι : Fin (ks v) → Fin (ns v),
          (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
            ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
              ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
        else φS v))
    (η : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (hη : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((η z : ℂˣ) : ℂ)) :
    ∫ g, φ g * chiDet (𝓞 L) L η g ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
      (∏ v ∈ T, ∑ ι : Fin (ks v) → Fin (ns v),
          ((NumberField.TateGlobal.localChar η (ws v).1
            (Matrix.GeneralLinearGroup.det ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)) : ℂˣ) : ℂ)) *
        ∫ g, {g : AdelicGL2 (𝓞 L) L |
              ∀ v ∉ S, semiLocalComponent K L v (glFin (𝓞 L) L g) ∈ semiLocalIntegralSet K L v}.indicator
            (fun g => φa (glArch (𝓞 L) L g) *
              ∏ v ∈ S, φS v (semiLocalComponent K L v (glFin (𝓞 L) L g))) g *
          chiDet (𝓞 L) L η g ∂(adelicGLHaar (Fin 2) (𝓞 L) L) := by sorry
