-- Prove2me | Theorems.Thm_AutomorphicForm_apply_centralScalar_eq_zero_of_not_exists_isNormOf_of_isUnitFactorization_of_prime
-- name    : AutomorphicForm.apply_centralScalar_eq_zero_of_not_exists_isNormOf_of_isUnitFactorization_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/ab3c8a2a-e42b-5d8f-9b03-e8d13a1a2305
-- title:
--   Vanishing at non-norm central ideles for matching test functions
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra whose degree $[L:K] = \operatorname{finrank}_K L$ is prime, and let $\sigma$ be a $K$-automorphism of $L$ with $\sigma \neq 1$. Let $S$ be a finite set of height-one primes of $\mathcal{O}_K$, and let $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$, $f_\infty$ on $\mathrm{GL}_2$ of the infinite adeles, $f_{\mathrm{fin}}$ on $\mathrm{GL}_2$ of the finite adeles, and a family $f_v$ on $\mathrm{GL}_2(K_v)$ indexed by all height-one primes $v$, be such that [`AutomorphicForm.IsUnitFactorization`](def/AutomorphicForm_TwistedOrbital.html#L526) holds: $f_\infty$ is of the form $\Phi \circ (\text{matrix entries in the mixed space of } K)$ for some $C^\infty$ function $\Phi$ and has compact support; $f_{\mathrm{fin}}$ is locally constant with compact support; $f_v$ is locally constant with compact support for $v \in S$; $f_{\mathrm{fin}}(h) = \prod_{v \in S} f_v(h_v)$ whenever $h_v$ lies in [`AutomorphicForm.localIntegralSet K v`](def/AutomorphicForm_LocalOrbitalBase.html#L100) (those $g \in \mathrm{GL}_2(K_v)$ with both $g$ and $g^{-1}$ having entries in $\mathcal{O}_v$) for every $v \notin S$, while $f_{\mathrm{fin}}(h) = 0$ as soon as $h_v$ lies outside that set for some $v \notin S$; and $f(g) = f_\infty(g_\infty) f_{\mathrm{fin}}(g_{\mathrm{fin}})$ for all $g$. Let $\varphi_v$ be functions on $\mathrm{GL}_2(L \otimes_K K_v)$ such that for $v \in S$ each $\varphi_v$ is locally constant with compact support and matches $f_v$ in the sense of [`AutomorphicForm.AreMatchingLocal`](def/AutomorphicForm_TwistedOrbital.html#L386) for $\sigma$, i.e. the `AreMatchingOn` relation taken with respect to the Haar measures [`AutomorphicForm.semiLocalHaar K L v`](def/AutomorphicForm_TwistedOrbital.html#L169) and [`AutomorphicForm.localHaar K v`](def/AutomorphicForm_LocalOrbitalBase.html#L168), and such that for every $v \notin S$ the indicator function of [`AutomorphicForm.semiLocalIntegralSet K L v`](def/AutomorphicForm_TwistedOrbital.html#L136) (the $g \in \mathrm{GL}_2(L \otimes_K K_v)$ with $g$ and $g^{-1}$ having entries in the image of $\mathcal{O}_L \otimes \mathcal{O}_v$) matches in the same sense the indicator function of [`AutomorphicForm.localIntegralSet K v`](def/AutomorphicForm_LocalOrbitalBase.html#L100). Finally, let $u$ be a unit of the adele ring of $K$ and assume that the scalar matrix $u \in \mathrm{GL}_2(\mathbb{A}_K)$ is not a norm: there is no $\delta \in \mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ and no $y$ with the image of the scalar matrix $u$ in $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ equal to $y^{-1} \cdot (\text{norm string of } \delta \text{ for } \sigma) \cdot y$. Then $f$ vanishes at the scalar matrix $u$.
--
--   This is the vanishing at the centre which, together with the local transfer at central elements, controls the central contributions in the comparison of trace formulas for cyclic base change of $\mathrm{GL}(2)$ in prime degree: the orbital integral of $f$ at a scalar is a volume factor times $f$ evaluated there, so the assertion is that these central orbital integrals vanish at the scalar ideles that are not norms from $L \otimes_K \mathbb{A}_K$. It is used by [`AutomorphicForm.areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime_of_factorization`](thm.html#AutomorphicForm.areMatchingOn_and_central_adeleRing_of_areMatchingAt_of_prime_of_factorization), which assembles the global matching statement at central elements from the local ones.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_apply_centralScalar_eq_zero_of_not_exists_isNormOf_of_isUnitFactorization_of_prime.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.apply_centralScalar_eq_zero_of_not_exists_isNormOf_of_isUnitFactorization_of_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hf : AutomorphicForm.IsUnitFactorization K S f fa ff fS)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφS : ∀ v ∈ S, AutomorphicForm.IsSemiLocalTestFn K L v (φS v))
    (hLoc : ∀ v ∈ S, AutomorphicForm.AreMatchingLocal K L v σ (φS v) (fS v))
    (hunit : ∀ v ∉ S, AutomorphicForm.AreMatchingLocal K L v σ
      ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
      ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)))
    (u : (AdeleRing (𝓞 K) K)ˣ)
    (hu : ¬ ∃ δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ (AutomorphicForm.centralScalar (𝓞 K) K u) δ) :
    f (AutomorphicForm.centralScalar (𝓞 K) K u) = 0 := by sorry
