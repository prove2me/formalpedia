-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isCompact_forall_idelicNorm_det_mul_mem_of_isSemiLocalFactorization_indicator_doubleCoset
-- name    : AutomorphicForm.exists_isCompact_forall_idelicNorm_det_mul_mem_of_isSemiLocalFactorization_indicator_doubleCoset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/a48f7ac2-d04e-560f-8083-34f67a20c1bd
-- title:
--   Determinant norms on the support lie in a fixed compact translate
-- statement:
--   Let $K$ and $L$ be number fields with $L/K$ Galois (and equality of finite places of $K$ decidable). Fix a finite set $S$ of height-one primes of $\mathcal{O}_K$, a function $\varphi_a$ on $\mathrm{GL}_2$ of the infinite adele ring of $L$, a family $\varphi_S$ of functions on $\mathrm{GL}_2(L\otimes_K K_v)$ indexed by the primes $v$ of $\mathcal{O}_K$, a further finite set $T$ of such primes, and for each $v$ a choice $w_v$ of a prime of $\mathcal{O}_L$ lying under-$\mathcal{O}_K$ over $v$. The assertion is that there is a compact set $C_0$ of ideles of $K$, chosen before any Hecke datum, with the following property. For every family $\rho$ with $\rho_v\in\mathrm{GL}_2(L_{w_v})$, every $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_L)$ and every $\varphi_f$ on $\mathrm{GL}_2$ of the finite adeles of $L$, suppose the triple $(\varphi,\varphi_a,\varphi_f)$ is a semi-local factorisation relative to $S\cup T$ with local data given by: the indicator function of the double coset $\mathcal{K}_v\cdot\{\text{semi-local component at }v\text{ of the image of }\rho_v\text{ under the local embedding into }\mathrm{GL}_2\text{ of the finite adeles of }L\}\cdot\mathcal{K}_v$ at $v\in T$, where $\mathcal{K}_v$ is the set of $g\in\mathrm{GL}_2(L\otimes_K K_v)$ such that $g$ and $g^{-1}$ have entries in the image of the tensor adic integers, and by $\varphi_S v$ at $v\notin T$. Here the factorisation hypothesis says: $\varphi_a$ is a smooth compactly supported function of the archimedean matrix entries, $\varphi_f$ is locally constant with compact support, each local datum at $v\in S\cup T$ is locally constant with compact support, $\varphi_f(h)=\prod_{v\in S\cup T}$ of the local data evaluated at the semi-local components of $h$ whenever all semi-local components of $h$ outside $S\cup T$ lie in $\mathcal{K}_v$, $\varphi_f(h)=0$ when some component outside $S\cup T$ fails this integrality, and $\varphi(g)=\varphi_a(\text{archimedean part of }g)\cdot\varphi_f(\text{finite part of }g)$. Then there is an idele $b$ of $K$ such that for every $g\in\mathrm{GL}_2(\mathbb{A}_L)$ with $\varphi(g)\neq 0$, the image of $\det g$ under the idelic norm of the genuine base change from $K$ to $L$, multiplied by $b$, lies in $C_0$.
--
--   This is the support-confinement step for Hecke double-coset test functions: the determinant of any point in the support of $\varphi$ has idelic norm in one fixed compact set up to a single translation, with the compact set independent of the Hecke datum $\rho$ while the translating idele (which absorbs the determinants at the places in $T$) is allowed to depend on it. It feeds the uniform volume estimate [`AutomorphicForm.exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure`](thm.html#AutomorphicForm.exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure) for orbital integrals over double cosets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isCompact_forall_idelicNorm_det_mul_mem_of_isSemiLocalFactorization_indicator_doubleCoset.lean

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

theorem AutomorphicForm.exists_isCompact_forall_idelicNorm_det_mul_mem_of_isSemiLocalFactorization_indicator_doubleCoset
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (T : Finset (HeightOneSpectrum (𝓞 K))) (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L)) :
    ∃ C₀ : Set (AdeleRing (𝓞 K) K)ˣ, IsCompact C₀ ∧
      ∀ (ρ : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                  semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) x
            else φS v) →
      ∃ b : (AdeleRing (𝓞 K) K)ˣ,
        ∀ g : AdelicGL2 (𝓞 L) L, φ g ≠ 0 →
          (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (Matrix.GeneralLinearGroup.det g) * b ∈ C₀ := by sorry
