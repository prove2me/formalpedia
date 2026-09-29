-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isSemiLocalFactorization_word
-- name    : AutomorphicForm.exists_isSemiLocalFactorization_word
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/2a49835e-e577-5ce6-b897-dbaaddfb3cbd
-- title:
--   Semi-local factorisation with word indicators at T
-- statement:
--   Let $L/K$ be an extension of number fields, let $S,T$ be finite sets of height-one primes of $\mathcal O_K$, let $\varphi_a : GL_2(L\otimes_{\mathbb Q}\mathbb R)\to\mathbb C$ (the infinite adèle ring of $L$) be an archimedean test factor, i.e. $\varphi_a$ is given by a smooth function of the matrix entries transported to the mixed space of $L$ and has compact support, and for every height-one prime $v$ of $\mathcal O_K$ let $\varphi_S(v) : GL_2(L\otimes_K K_v)\to\mathbb C$ be given, assumed locally constant with compact support for $v\in S$ with $v\notin T$. Further data are fixed for every $v$: an extension $w_v$ of $v$ to a height-one prime of $\mathcal O_L$, a natural number $n_v$, elements $r_v(0),\dots,r_v(n_v-1)$ and $z_v$ of $GL_2(L_{w_v})$, and natural numbers $k_v$, $j_v$. The conclusion asserts the existence of $\varphi : GL_2(\mathbb A_L)\to\mathbb C$ and $\varphi_f : GL_2(\mathbb A_{L,f})\to\mathbb C$ such that the predicate `IsSemiLocalFactorization` holds for the set $S\cup T$, the pair $(\varphi_a,\varphi_f)$ and the family of semi-local factors which at $v\in T$ is $x\mapsto \sum_{\iota : \mathrm{Fin}(k_v)\to \mathrm{Fin}(n_v)} \mathbf 1_{\Omega_v}\bigl(c_v(\iota)^{-1}x\bigr)$, where $\Omega_v$ is the set of $g\in GL_2(L\otimes_K K_v)$ with $g$ and $g^{-1}$ having entries in the image of $\mathcal O_L\otimes \mathcal O_{K_v}$, and $c_v(\iota)$ is the $v$-semi-local component of the image under [`AdelicDock.localEmbed`](def/AdelicDock_LocalEmbedding.html#L97) at $w_v$ of the word $r_v(\iota(0))\cdots r_v(\iota(k_v-1))\,z_v^{j_v}$, and at $v\notin T$ is $\varphi_S(v)$. That is: $\varphi_a$ is an archimedean test factor, $\varphi_f$ is locally constant with compact support, each of the listed factors at $v\in S\cup T$ is locally constant with compact support, $\varphi_f(h)=\prod_{v\in S\cup T}\varphi_v(h_v)$ whenever all semi-local components of $h$ outside $S\cup T$ lie in $\Omega_v$, $\varphi_f(h)=0$ if some component outside $S\cup T$ fails to do so, and $\varphi(g)=\varphi_a(g_\infty)\,\varphi_f(g_f)$.
--
--   This is the Schwartz–Bruhat input for the unipotent term in the adelic trace computation: it produces a global test function on $GL_2(\mathbb A_L)$ that factorises semi-locally over $K$, is the standard integrality indicator away from $S\cup T$, equals the prescribed factors at $v\in S\setminus T$, and at the places of $T$ is a finite sum of translates of the integrality indicator indexed by words of fixed length in prescribed local matrices times a power of a further local matrix. It is used in the identification of the transversal pieces of the unipotent term via [`AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_tracePushforward_eq_indicator_prod_twistedLocalFactor_unram`](thm.html#AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_tracePushforward_eq_indicator_prod_twistedLocalFactor_unram).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isSemiLocalFactorization_word.lean

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
import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_AutomorphicForm_AdelicTracePushforward

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm.AdelicTracePushforward
open scoped ENNReal

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_isSemiLocalFactorization_word
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : IsArchTestFactor L φa)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφS : ∀ v ∈ S, v ∉ T → IsSemiLocalTestFn K L v (φS v))
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (ns : HeightOneSpectrum (𝓞 K) → ℕ)
    (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L))
    (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
    (ks js : HeightOneSpectrum (𝓞 K) → ℕ) :
    ∃ (φ : AdelicGL2 (𝓞 L) L → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
      IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) := by sorry
