-- Prove2me | Theorems.Thm_AutomorphicForm_sum_relIndex_mul_twistedConj_diagonal_eq_zpow_absNorm_mul_finsum_of_ramificationIdx_eq_one
-- name    : AutomorphicForm.sum_relIndex_mul_twistedConj_diagonal_eq_zpow_absNorm_mul_finsum_of_ramificationIdx_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/4bd96236-a4b6-5873-ac00-daec8f7e8434
-- title:
--   Twisted orbital sum at an unramified place
-- statement:
--   Let $K$ be a number field, $v$ a nonzero prime of $\mathcal O_K$, and let $L$ be a number field which is a $K$-algebra together with $w$ a nonzero prime of $\mathcal O_L$ whose contraction to $\mathcal O_K$ is $v$; assume $\mathrm{ramificationIdx}'$ of the pair (the contraction of $w$, $w$) equals $1$. Write $K_v$ and $L_w$ for the adic completions and $U =$ [`LocalGL2.integralSubgroup`](def/LocalLanglands_LocalHeckeInstance.html#L13), the image of $\mathrm{GL}_2$ of the $w$-adic integers inside $\mathrm{GL}_2(L_w)$ under the map induced by the inclusion of rings. Let $\theta$ be a $K_v$-algebra automorphism of $L_w$ whose fixed points are exactly the elements in the image of $K_v$, and let $\varphi$ lie in the $\mathbb C$-submodule of functions $\mathrm{GL}_2(L_w) \to \mathbb C$ cut out by the predicate `IsHeckeFun` relative to $U$. Let $a,b \in L_w^{\times}$ and $\alpha,\beta \in K_v^{\times}$ be such that $\alpha$ and $\beta$, viewed in $L_w$, equal $\prod_{i<n}\theta^i(a)$ and $\prod_{i<n}\theta^i(b)$ with $n = [L_w:K_v]$, and let $m \in \mathbb Z$ satisfy $\mathrm{v}(1-\beta/\alpha) = \mathrm{ofAdd}(-m)$ for the valuation on $K_v$. Let $\delta \in \mathrm{GL}_2(L_w)$ have matrix $\mathrm{diag}(a,b)$, let $T$ be a subgroup whose elements are exactly the $x$ with $x^{-1}\delta\,\theta(x) = \delta$ ($\theta$ applied entrywise), and let $S$ be a finite subset of $\mathrm{GL}_2(L_w)$ meeting each double coset $TxU$ at most once and such that every $x$ with $\varphi(x^{-1}\delta\,\theta(x)) \neq 0$ lies in $TsU$ for some $s \in S$. Then $$\sum_{x \in S} \big[\,T\cap U : (T \cap xUx^{-1})\cap(T\cap U)\,\big]\cdot \varphi\!\left(x^{-1}\delta\,\theta(x)\right) = N(v)^{m}\sum^{f}_{c \in \mathrm{GL}_2(L_w)/U} \mathbf 1_{E}(c)\,\varphi(\mathrm{out}(c)),$$ where $N(v)$ is the absolute norm of $v$, the sum on the right is a `finsum` over the coset space, $E$ is the set of cosets $c$ admitting a representative $g$ with $g_{1,0} = 0$, $g_{0,0} = a$ and $g_{1,1} = b$, and $\mathrm{out}(c)$ is the chosen representative of $c$.
--
--   This is an unfolding identity for the $\theta$-twisted orbital sum of a Hecke function on $\mathrm{GL}_2$ over a local field: the double-coset sum weighted by relative stabiliser indices is computed as a power of the residue-field size times the sum of $\varphi$ over the cosets containing an upper triangular matrix with prescribed diagonal $(a,b)$. It is used, via the Iwasawa decomposition with diagonal middle term [`LocalGL2.iwasawa_decomposition_diag`](thm.html#LocalGL2.iwasawa_decomposition_diag), in the construction of a local matching of Hecke actions at an inert prime ([`AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime`](thm.html#AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_sum_relIndex_mul_twistedConj_diagonal_eq_zpow_absNorm_mul_finsum_of_ramificationIdx_eq_one.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LocalLanglands_LocalHeckeInstance

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem
AutomorphicForm.sum_relIndex_mul_twistedConj_diagonal_eq_zpow_absNorm_mul_finsum_of_ramificationIdx_eq_one
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (L : Type) [Field L] [NumberField L] [Algebra K L] (w : v.Extension (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : ∀ x : w.1.adicCompletion L,
      θ x = x ↔ x ∈ Set.range (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)))
    (φ : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ)
    (a b : (w.1.adicCompletion L)ˣ) (α β : (v.adicCompletion K)ˣ)
    (hα : algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (α : v.adicCompletion K) =
      ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
        (θ ^ i) (a : w.1.adicCompletion L))
    (hβ : algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (β : v.adicCompletion K) =
      ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
        (θ ^ i) (b : w.1.adicCompletion L))
    (m : ℤ)
    (hm : Valued.v ((1 : v.adicCompletion K) - (β : v.adicCompletion K) / (α : v.adicCompletion K)) =
      ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (δ : GL (Fin 2) (w.1.adicCompletion L))
    (hδ : (δ : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      !![(a : w.1.adicCompletion L), 0; 0, (b : w.1.adicCompletion L)])
    (T : Subgroup (GL (Fin 2) (w.1.adicCompletion L)))
    (hT : ∀ x : GL (Fin 2) (w.1.adicCompletion L),
      x ∈ T ↔ x⁻¹ * δ * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x = δ)
    (S : Finset (GL (Fin 2) (w.1.adicCompletion L)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ T,
      ∀ u ∈ LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L),
        s' = t * s * u → s' = s)
    (hcov : ∀ x : GL (Fin 2) (w.1.adicCompletion L),
      (φ : GL (Fin 2) (w.1.adicCompletion L) → ℂ)
          (x⁻¹ * δ * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x) ≠ 0 →
        ∃ s ∈ S, ∃ t ∈ T,
          ∃ u ∈ LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L), x = t * s * u) :
    ∑ x ∈ S,
        (((T ⊓ (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)).map
              (MulAut.conj x).toMonoidHom).relIndex
            (T ⊓ LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) : ℕ) : ℂ) *
          (φ : GL (Fin 2) (w.1.adicCompletion L) → ℂ)
            (x⁻¹ * δ * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x) =
      (Ideal.absNorm v.asIdeal : ℂ) ^ m *
        ∑ᶠ c : GL (Fin 2) (w.1.adicCompletion L) ⧸
          LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L),
        Set.indicator
          {c : GL (Fin 2) (w.1.adicCompletion L) ⧸
              LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) |
            ∃ g : GL (Fin 2) (w.1.adicCompletion L), QuotientGroup.mk g = c ∧
              (g : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 1 0 = 0 ∧
              (g : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 0 0 = (a : w.1.adicCompletion L) ∧
              (g : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 1 1 = (b : w.1.adicCompletion L)}
          (fun c => (φ : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (Quotient.out c)) c := by sorry
