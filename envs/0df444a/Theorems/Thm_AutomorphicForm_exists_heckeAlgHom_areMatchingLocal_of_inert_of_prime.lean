-- Prove2me | Theorems.Thm_AutomorphicForm_exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime
-- name    : AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/c45dbd6b-619a-5bda-be43-4e1df1803f01
-- title:
--   Spherical base change matching at an inert place, prime degree
-- statement:
--   Let $K \subseteq L$ be number fields with $n = [L:K]$ prime, let $\sigma$ be a non-trivial $K$-automorphism of $L$, let $v$ be a nonzero prime of $\mathcal O_K$ and $w$ a nonzero prime of $\mathcal O_L$ lying over $v$ (an element of `v.Extension`) whose ramification index over the prime of $\mathcal O_K$ beneath it is $1$, and let $e$ be an isomorphism of $K_v$-algebras $L \otimes_K K_v \cong L_w$. Fix irreducible elements $\varpi_K$, $\varpi_L$ of the valuation rings $\mathcal O_v$, $\mathcal O_w$ with nonzero images in $K_v$, $L_w$, and let $U_K$, $U_L$ be the images of $\mathrm{GL}_2(\mathcal O_v)$, $\mathrm{GL}_2(\mathcal O_w)$ in $\mathrm{GL}_2(K_v)$, $\mathrm{GL}_2(L_w)$ under the structure maps ([`LocalGL2.integralSubgroup`](def/LocalLanglands_LocalHeckeInstance.html#L13)). In the Hecke algebra of $U_K$-bi-invariant functions with values in $\mathbb C$, let $T_K$ be the indicator of the double coset $U_K\,\mathrm{diag}(\varpi_K,1)\,U_K$ and $E_K$ be $N(v)$ times the indicator of $\{x : x = \varpi_K u \text{ as matrices, some } u \in U_K\}$, $N(v)$ the absolute norm of $v$; let $T_L$, $E_L$ be the corresponding elements for $U_L$ and $\varpi_L$. Let $p : \mathbb N \to$ (Hecke algebra of $U_K$) satisfy $p_0 = 2$, $p_1 = T_K$ and $p_{k+2} = T_K p_{k+1} - E_K p_k$. Then there is a $\mathbb C$-algebra homomorphism $b$ from the Hecke algebra of $U_L$ to that of $U_K$ with $b(T_L) = p_n$, $b(E_L) = E_K^{\,n}$, and such that for every $\varphi$ in the Hecke algebra of $U_L$ the function on $\mathrm{GL}_2(L \otimes_K K_v)$ obtained by transporting $\varphi$ along $e$ and the function $b(\varphi)$ on $\mathrm{GL}_2(K_v)$ satisfy `AreMatchingLocal K L v σ`: with respect to the Haar measure on $\mathrm{GL}_2(L \otimes_K K_v)$ normalised on the semi-local integral compact subgroup and the Haar measure on $\mathrm{GL}_2(K_v)$ normalised on the local integral compact subgroup, every twisted orbital integral of the transported $\varphi$ at a $\delta$ whose $\sigma$-norm string is regular semisimple equals the orbital integral of $b(\varphi)$ at any regular semisimple $\gamma$ that is a norm of $\delta$ via a norm conjugator, for coupled Haar measures on the centraliser of $\gamma$ and the twisted centraliser of $\delta$, while the orbital integral of $b(\varphi)$ vanishes at every regular semisimple $\gamma$ that is not a norm.
--
--   This is the spherical fundamental lemma for base change of $\mathrm{GL}_2$ at a place inert in an extension of prime degree: the hypotheses on the ramification index and on $e$ say that $v$ has a single unramified extension $w$, and $b$ is the base change homomorphism of spherical Hecke algebras, sending the Hecke operator $T_L$ to the $n$-th power-sum polynomial in $T_K$, $E_K$. It is used in the project to produce matching functions at inert places, in particular for the indicator function of the semi-local integral set and for Hecke words, and in the twisted trace computation that locates cusp classes of principal level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LocalLanglands_HeckeCosetLocal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime)
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (e : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (ϖK : v.adicCompletionIntegers K) (hϖK : Irreducible ϖK)
    (hϖK0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK ≠ 0)
    (ϖL : w.1.adicCompletionIntegers L) (hϖL : Irreducible ϖL)
    (hϖL0 : algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖL ≠ 0)
    (UK : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hUK : UK = LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
    (UL : Subgroup (GL (Fin 2) (w.1.adicCompletion L)))
    (hUL : UL = LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))
    (TK EK : HeckePair.HeckeAlgebra UK ℂ)
    (hTK : (TK : GL (Fin 2) (v.adicCompletion K) → ℂ) =
      (HeckePair.doubleCoset UK (LocalGL2.diagPi ϖK hϖK0)).indicator fun _ => (1 : ℂ))
    (hEK : (EK : GL (Fin 2) (v.adicCompletion K) → ℂ) =
      (Ideal.absNorm v.asIdeal : ℂ) •
        ({x : GL (Fin 2) (v.adicCompletion K) | ∃ u ∈ UK,
            (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
              algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK •
                (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))}.indicator fun _ => (1 : ℂ)))
    (TL EL : HeckePair.HeckeAlgebra UL ℂ)
    (hTL : (TL : GL (Fin 2) (w.1.adicCompletion L) → ℂ) =
      (HeckePair.doubleCoset UL (LocalGL2.diagPi ϖL hϖL0)).indicator fun _ => (1 : ℂ))
    (hEL : (EL : GL (Fin 2) (w.1.adicCompletion L) → ℂ) =
      (Ideal.absNorm w.1.asIdeal : ℂ) •
        ({x : GL (Fin 2) (w.1.adicCompletion L) | ∃ u ∈ UL,
            (x : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
              algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖL •
                (u : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L))}.indicator fun _ => (1 : ℂ)))
    (p : ℕ → HeckePair.HeckeAlgebra UK ℂ) (hp0 : p 0 = 2) (hp1 : p 1 = TK)
    (hp : ∀ k : ℕ, p (k + 2) = TK * p (k + 1) - EK * p k) :
    ∃ b : HeckePair.HeckeAlgebra UL ℂ →ₐ[ℂ] HeckePair.HeckeAlgebra UK ℂ,
      b TL = p (Module.finrank K L) ∧ b EL = EK ^ Module.finrank K L ∧
      ∀ φ : HeckePair.HeckeAlgebra UL ℂ,
        AreMatchingLocal K L v σ
          (fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            (φ : GL (Fin 2) (w.1.adicCompletion L) → ℂ)
              (Matrix.GeneralLinearGroup.map e.toAlgHom.toRingHom g))
          (b φ : GL (Fin 2) (v.adicCompletion K) → ℂ) := by sorry
