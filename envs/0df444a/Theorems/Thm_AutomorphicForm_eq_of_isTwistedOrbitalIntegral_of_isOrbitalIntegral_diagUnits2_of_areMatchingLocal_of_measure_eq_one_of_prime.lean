-- Prove2me | Theorems.Thm_AutomorphicForm_eq_of_isTwistedOrbitalIntegral_of_isOrbitalIntegral_diagUnits2_of_areMatchingLocal_of_measure_eq_one_of_prime
-- name    : AutomorphicForm.eq_of_isTwistedOrbitalIntegral_of_isOrbitalIntegral_diagUnits2_of_areMatchingLocal_of_measure_eq_one_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/4dfe135a-43ca-5a7f-b793-2f7a3a5edc30
-- title:
--   Local matching at a split regular norm pair of prime degree
-- statement:
--   Let $K$ and $L$ be number fields with $L/K$ a finite Galois extension, let $\sigma \in \mathrm{Gal}(L/K)$ be such that every element of the Galois group lies in the subgroup of integral powers of $\sigma$, assume $[L:K]$ is prime and $\sigma \neq 1$, and let $v$ be a nonzero prime of $\mathcal{O}_K$. Let $\varphi_v : \mathrm{GL}_2(L \otimes_K K_v) \to \mathbb{C}$ and $f_v : \mathrm{GL}_2(K_v) \to \mathbb{C}$ be locally constant with compact support, and assume the pair $(\varphi_v, f_v)$ satisfies [`AutomorphicForm.AreMatchingLocal`](def/AutomorphicForm_TwistedOrbital.html#L386) for $\sigma$, i.e. the matching relation `AreMatchingOn` with respect to the semi-local Haar measure on $\mathrm{GL}_2(L \otimes_K K_v)$ and the local Haar measure on $\mathrm{GL}_2(K_v)$. Let $a \neq b$ be units of $K_v$ and $\alpha, \beta$ units of $L \otimes_K K_v$ such that the norm string $\prod_{i<[L:K]} \sigma^i(\delta)$ of $\delta = \mathrm{diag}(\alpha,\beta)$ equals the image of $\gamma = \mathrm{diag}(a,b)$ under the entrywise map induced by $K_v \to L \otimes_K K_v$. Let $\tau$ be a Haar measure on the centraliser of $\gamma$ in $\mathrm{GL}_2(K_v)$ giving mass $1$ to those of its elements $g$ with $g$ and $g^{-1}$ having entries in $\mathcal{O}_v$, and let $\tau'$ be a Haar measure on the $\sigma$-twisted centraliser of $\delta$ giving mass $1$ to those of its elements integral in the same sense over the semi-local integers. Then any complex number $I'$ that is a twisted orbital integral of $\varphi_v$ at $\delta$ with respect to $\tau'$ equals any complex number $I$ that is an orbital integral of $f_v$ at $\gamma$ with respect to $\tau$ (the latter meaning $I = \int f_v(x^{-1}\gamma x)\, w(x)$ against the local Haar measure for some section weight $w$).
--
--   This is the local matching identity of base change for $\mathrm{GL}(2)$ in the split regular case: at a place where the norm of a diagonal twisted conjugacy class is a regular split element, the twisted orbital integral of $\varphi_v$ and the orbital integral of the matching function $f_v$ coincide once the measures on the two centralisers are normalised to give mass one to the integral points. It feeds the comparison of trace formulae used in the Langlands–Tunnell input to the argument, being cited in the construction of Satake/Hecke data at unramified places and in the affine winding estimate.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eq_of_isTwistedOrbitalIntegral_of_isOrbitalIntegral_diagUnits2_of_areMatchingLocal_of_measure_eq_one_of_prime.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.eq_of_isTwistedOrbitalIntegral_of_isOrbitalIntegral_diagUnits2_of_areMatchingLocal_of_measure_eq_one_of_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hprime : (Module.finrank K L).Prime) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφv : AutomorphicForm.IsSemiLocalTestFn K L v φv)
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : AutomorphicForm.IsLocalTestFn K v fv)
    (hmatch : AutomorphicForm.AreMatchingLocal K L v σ φv fv)
    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b)
    (α β : (L ⊗[K] v.adicCompletion K)ˣ)
    (hN : AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a b))
    (τ : @Measure (AutomorphicForm.localCentralizer K v (diagUnits2 a b))
      (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)) τ)
    (hτ1 : τ {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} = 1)
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)))
    (hτ' : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ')
    (hτ'1 : τ' {t | (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈
      AutomorphicForm.semiLocalIntegralSet K L v} = 1)
    (I I' : ℂ)
    (hI : AutomorphicForm.IsOrbitalIntegral K v (diagUnits2 a b) τ fv I)
    (hI' : AutomorphicForm.IsTwistedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φv I') :
    I' = I := by sorry
