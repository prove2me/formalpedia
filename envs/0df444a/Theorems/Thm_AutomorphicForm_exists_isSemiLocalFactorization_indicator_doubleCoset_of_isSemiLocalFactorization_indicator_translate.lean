-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isSemiLocalFactorization_indicator_doubleCoset_of_isSemiLocalFactorization_indicator_translate
-- name    : AutomorphicForm.exists_isSemiLocalFactorization_indicator_doubleCoset_of_isSemiLocalFactorization_indicator_translate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/e95ae537-8104-5f6a-b6f3-202cb104b87f
-- title:
--   Double-coset test function from its unit-coset translate
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, fix decidable equality on the height-one spectrum of $\mathcal O_K$, and let $S$ and $T$ be finite sets of height-one primes of $\mathcal O_K$. Fix $\varphi_a : \mathrm{GL}_2(L\otimes_{\mathbb Q}\mathbb R) \to \mathbb C$ on the infinite adelic points, a family $\varphi_S$ assigning to every $v$ a function on $\mathrm{GL}_2(L\otimes_K K_v)$, for every $v$ an extension $w_v$ of $v$ to $\mathcal O_L$ (a height-one prime of $\mathcal O_L$ lying under $v$) together with $\rho_v \in \mathrm{GL}_2(L_{w_v})$, and functions $\varphi$ on $\mathrm{GL}_2$ of the full adele ring of $L$ and $\varphi_f$ on $\mathrm{GL}_2$ of the finite adele ring. Write $\tilde\rho_v$ for the image of $\rho_v$ under [`AdelicDock.localEmbed`](def/AdelicDock_LocalEmbedding.html#L97), placing $\rho_v$ at $w_v$ and the identity elsewhere, followed by `semiLocalComponent K L v`, and $\mathcal K_v =$ `semiLocalIntegralSet K L v`, the set of $g \in \mathrm{GL}_2(L\otimes_K K_v)$ such that both $g$ and $g^{-1}$ have entries in the image of $\mathcal O_L \otimes \mathcal O_{K_v}$. Assume `IsSemiLocalFactorization K L (S ∪ T) φ φa φf` holds for the family whose value at $v \in T$ is $x \mapsto \mathbf 1_{\mathcal K_v}(\tilde\rho_v^{-1}x)$ and at $v \notin T$ is $\varphi_S\,v$; that is: $\varphi_a$ agrees with a smooth compactly supported function of the archimedean matrix entries and has compact support; $\varphi_f$ is locally constant with compact support; each member of the family at a place of $S\cup T$ is locally constant with compact support; $\varphi_f(h)$ equals the product over $v \in S\cup T$ of the family's value at the semi-local component of $h$ whenever all components of $h$ outside $S\cup T$ lie in the corresponding $\mathcal K_v$, and $\varphi_f(h)=0$ when some component outside $S\cup T$ fails to; and $\varphi(g) = \varphi_a(g_\infty)\varphi_f(g_{\mathrm{fin}})$. The conclusion is that there exist $\varphi'$ and $\varphi_f'$ satisfying the same predicate `IsSemiLocalFactorization K L (S ∪ T) φ' φa φf'` for the family whose value at $v \in T$ is the indicator of the double coset $\mathcal K_v \{\tilde\rho_v\} \mathcal K_v$ and at $v \notin T$ is $\varphi_S\,v$.
--
--   This replaces, at the finitely many places of $T$, the indicator of a single left translate $\tilde\rho_v\mathcal K_v$ by the indicator of the Hecke double coset $\mathcal K_v\tilde\rho_v\mathcal K_v$, producing the test function whose adelic orbital integrals compute the Hecke operator at those places. It is used in the estimate [`AutomorphicForm.exists_forall_sum_lintegral_orbital_add_weightedOrbital_le_of_isSemiLocalFactorization_indicator_translate`](thm.html#AutomorphicForm.exists_forall_sum_lintegral_orbital_add_weightedOrbital_le_of_isSemiLocalFactorization_indicator_translate).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isSemiLocalFactorization_indicator_doubleCoset_of_isSemiLocalFactorization_indicator_translate.lean

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

theorem AutomorphicForm.exists_isSemiLocalFactorization_indicator_doubleCoset_of_isSemiLocalFactorization_indicator_translate
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (T : Finset (HeightOneSpectrum (𝓞 K))) (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (ρ : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (hφ : IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))⁻¹ * x)
            else φS v)) :
    ∃ (φ' : AdelicGL2 (𝓞 L) L → ℂ) (φf' : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
      IsSemiLocalFactorization K L (S ∪ T) φ' φa φf'
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                  semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) x
            else φS v) := by sorry
