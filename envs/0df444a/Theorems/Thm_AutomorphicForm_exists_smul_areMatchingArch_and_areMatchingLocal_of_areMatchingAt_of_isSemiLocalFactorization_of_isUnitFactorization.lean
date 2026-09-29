-- Prove2me | Theorems.Thm_AutomorphicForm_exists_smul_areMatchingArch_and_areMatchingLocal_of_areMatchingAt_of_isSemiLocalFactorization_of_isUnitFactorization
-- name    : AutomorphicForm.exists_smul_areMatchingArch_and_areMatchingLocal_of_areMatchingAt_of_isSemiLocalFactorization_of_isUnitFactorization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/18033d4c-805d-5f50-a65b-e8f36638f602
-- title:
--   Matching descends to any factorisations, up to reciprocal scalars
-- statement:
--   Let $K \subseteq L$ be number fields, $\sigma$ a $K$-algebra automorphism of $L$, and $S$ a finite set of height-one primes of $\mathcal O_K$. Let $\varphi : \mathrm{GL}_2(\mathbb A_L) \to \mathbb C$ together with $\varphi_a$ on $\mathrm{GL}_2$ of the infinite adeles of $L$, $\varphi_f$ on $\mathrm{GL}_2$ of the finite adeles of $L$ and a family $\varphi_S(v)$ on $\mathrm{GL}_2(L \otimes_K K_v)$ satisfy `IsSemiLocalFactorization`: $\varphi_a$ is an archimedean test factor (a compactly supported function given by a smooth function of the matrix entries viewed in the mixed space), $\varphi_f$ is locally constant with compact support, each $\varphi_S(v)$ for $v \in S$ is locally constant with compact support, $\varphi_f$ is the product over $v \in S$ of the $\varphi_S(v)$ at the semi-local components when all components outside $S$ are integral and vanishes otherwise, and $\varphi$ is the product of $\varphi_a$ and $\varphi_f$ on the archimedean and finite parts. Let $f$ on $\mathrm{GL}_2(\mathbb A_K)$ with $f_a$, $f_f$, $f_S$ satisfy the corresponding `IsUnitFactorization` condition over $K$, with local factors $f_S(v)$ on $\mathrm{GL}_2(K_v)$. Assume `AreMatchingAt`, i.e. some such pair of factorisations of $\varphi$ and $f$ exists which matches archimedean orbital integrals and matches locally at every $v \in S$; assume also $\varphi \not\equiv 0$ and $f \not\equiv 0$. Then there are $\rho_a \in \mathbb C$ and $\rho : \{\text{primes}\} \to \mathbb C$ with $\rho_a \neq 0$, $\rho(v) \neq 0$ for $v \in S$, and $\rho_a \prod_{v \in S} \rho(v) = 1$, such that $\rho_a \cdot f_a$ is again an archimedean test factor, each $\rho(v) \cdot f_S(v)$ ($v \in S$) is locally constant with compact support, $\varphi_a$ and $\rho_a \cdot f_a$ satisfy `AreMatchingArch`, and $\varphi_S(v)$ and $\rho(v) \cdot f_S(v)$ satisfy `AreMatchingLocal` for every $v \in S$. Here the matching relations assert, for the relevant Haar measures on $\mathrm{GL}_2$, that the twisted orbital integral of the $L$-side function at any $\delta$ with regular semisimple norm agrees with the orbital integral of the $K$-side function at any regular semisimple $\gamma$ linked to $\delta$ by a norm conjugator and coupled Haar measures on the centraliser and the twisted centraliser, and that the orbital integral of the $K$-side function vanishes at regular semisimple $\gamma$ which are not norms.
--
--   This is the statement that the transfer (matching) of test functions between $\mathrm{GL}_2$ over $L$ and over $K$ is independent of the chosen semi-local/unit factorisations: any prescribed pair of factorisations of the same non-zero $\varphi$ and $f$ matches after rescaling the ground factors by non-zero scalars whose product is $1$. It is used in the comparison of twisted and untwisted trace formulae feeding the base-change argument, via the winding/intercept computation that cites it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_smul_areMatchingArch_and_areMatchingLocal_of_areMatchingAt_of_isSemiLocalFactorization_of_isUnitFactorization.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

open scoped TensorProduct in

theorem AutomorphicForm.exists_smul_areMatchingArch_and_areMatchingLocal_of_areMatchingAt_of_isSemiLocalFactorization_of_isUnitFactorization
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφ : AutomorphicForm.IsSemiLocalFactorization K L S φ φa φf φS)
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hf : AutomorphicForm.IsUnitFactorization K S f fa ff fS)
    (hm : AutomorphicForm.AreMatchingAt K L σ S φ f)

    (hφ0 : ∃ g, φ g ≠ 0) (hf0 : ∃ g, f g ≠ 0) :
    ∃ (ρa : ℂ) (ρ : HeightOneSpectrum (𝓞 K) → ℂ),
      ρa ≠ 0 ∧ (∀ v ∈ S, ρ v ≠ 0) ∧ ρa * ∏ v ∈ S, ρ v = 1 ∧
      AutomorphicForm.IsArchTestFactor K (ρa • fa) ∧ (∀ v ∈ S, AutomorphicForm.IsLocalTestFn K v (ρ v • fS v)) ∧
      AutomorphicForm.AreMatchingArch K L σ φa (ρa • fa) ∧
      ∀ v ∈ S, AutomorphicForm.AreMatchingLocal K L v σ (φS v) (ρ v • fS v) := by sorry
