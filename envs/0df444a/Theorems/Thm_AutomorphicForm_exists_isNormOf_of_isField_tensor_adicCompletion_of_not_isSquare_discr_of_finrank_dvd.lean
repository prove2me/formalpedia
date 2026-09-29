-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd
-- name    : AutomorphicForm.exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/d52ca384-cf66-58f8-89da-b45c85e2dcd2
-- title:
--   Inert case: elliptic γ is a σ-twisted norm
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and assume the degree $n = \operatorname{finrank}_K L$ is prime. Let $\sigma$ be a $K$-algebra automorphism of $L$ with $\sigma \neq 1$, and let $v$ be a height one prime of the ring of integers $\mathcal{O}_K$. Assume: every height one prime $w$ of $\mathcal{O}_L$ whose contraction `HeightOneSpectrum.under (𝓞 K) w` equals $v$ satisfies $\operatorname{ramificationIdx}'$ of $w$ over that contraction equal to $1$; and the $K_v$-algebra $L \otimes_K K_v$ is a field, where $K_v$ denotes `v.adicCompletion K`. Let $\gamma \in \mathrm{GL}_2(K_v)$ be such that the discriminant $\operatorname{tr}(\gamma)^2 - 4\det(\gamma)$ of its characteristic polynomial is not a square in $K_v$, and such that the valuation of $\det \gamma$ lies in $n\mathbb{Z}$: there is $k \in \mathbb{Z}$ with $\mathrm{v}(\det \gamma) = \mathrm{ofAdd}(nk)$ in $\mathbb{Z}_{\ge 0}$-valued form, i.e. in $\mathrm{WithZero}(\mathrm{Multiplicative}\,\mathbb{Z})$. Then there exists $\delta \in \mathrm{GL}_2(L \otimes_K K_v)$ with `IsNormOf K L (v.adicCompletion K) σ γ δ`, that is, there exists $y \in \mathrm{GL}_2(L \otimes_K K_v)$ such that the image `toTensorGL K L (v.adicCompletion K) γ` of $\gamma$ equals $y^{-1} \cdot \mathrm{normString}\,K\,L\,(v.\mathrm{adicCompletion}\,K)\,\sigma\,\delta \cdot y$, the $\sigma$-twisted norm string of $\delta$.
--
--   This is the inert local case of the statement that an elliptic conjugacy class in $\mathrm{GL}_2(K_v)$ whose determinant has valuation divisible by the prime degree $[L:K]$ comes from a $\sigma$-twisted norm over $L \otimes_K K_v$, the local input to base change for $\mathrm{GL}(2)$ along a cyclic extension of prime degree. It is used, together with the split case, by [`AutomorphicForm.exists_isNormOf_of_not_isSquare_discr_of_finrank_dvd_of_ramificationIdx_eq_one`](thm.html#AutomorphicForm.exists_isNormOf_of_not_isSquare_discr_of_finrank_dvd_of_ramificationIdx_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem AutomorphicForm.exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime)
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (hA : IsField (L ⊗[K] v.adicCompletion K))
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : ¬ IsSquare (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
      4 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))))
    (hdet : ∃ k : ℤ, Valued.v (Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) =
      ((Multiplicative.ofAdd ((Module.finrank K L : ℤ) * k) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    ∃ δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K), IsNormOf K L (v.adicCompletion K) σ γ δ := by sorry
