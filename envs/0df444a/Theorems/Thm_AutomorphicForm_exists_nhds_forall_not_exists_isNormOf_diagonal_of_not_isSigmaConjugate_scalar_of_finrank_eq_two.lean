-- Prove2me | Theorems.Thm_AutomorphicForm_exists_nhds_forall_not_exists_isNormOf_diagonal_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
-- name    : AutomorphicForm.exists_nhds_forall_not_exists_isNormOf_diagonal_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/481f8a51-e024-57be-a759-86185668924e
-- title:
--   Split regular elements near a non-norm scalar are no norms
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an extension of $K$ of degree $\operatorname{finrank}_K L = 2$, let $\sigma$ be a $K$-algebra automorphism of $L$, and assume $\sigma$ generates the whole automorphism group, in the sense that every $\tau : L \simeq_K L$ lies in the subgroup of integer powers of $\sigma$. Let $v$ be a height-one prime of $\mathcal{O}_K$, write $K_v$ for the $v$-adic completion of $K$ and $E = L \otimes_K K_v$, with $\sigma$ acting on $E$ through the first factor. Let $c \in K_v^\times$ and let $\delta \in \mathrm{GL}_2(E)$ be such that the scalar matrix $c \cdot 1_2 \in \mathrm{GL}_2(K_v)$ is a norm of $\delta$, i.e. there is $y \in \mathrm{GL}_2(E)$ with the image of $c\cdot 1_2$ under the base-change map `toTensorGL` equal to $y^{-1} \cdot \mathrm{normString}\,\delta \cdot y$, where $\mathrm{normString}$ denotes the norm string of $\delta$ relative to $\sigma$. Suppose moreover that $\delta$ is $\sigma$-conjugate to no scalar: for every $z \in E^\times$ there is no $x \in \mathrm{GL}_2(E)$ with $z \cdot 1_2 = x^{-1}\,\delta\,\sigma(x)$, $\sigma$ acting entrywise. Then there is a neighbourhood $U$ of $1$ in $K_v$ such that for every unit $a$ of $K_v$ with $a \in U$ and $a^2 \neq 1$, and every $\gamma \in \mathrm{GL}_2(K_v)$ whose underlying matrix is $\operatorname{diag}(ca, ca^{-1})$, no $\delta' \in \mathrm{GL}_2(E)$ has $\gamma$ as a norm, i.e. there is no $\delta'$ and no $y' \in \mathrm{GL}_2(E)$ with the image of $\gamma$ in $\mathrm{GL}_2(E)$ equal to $y'^{-1} \cdot \mathrm{normString}\,\delta' \cdot y'$.
--
--   This is the local statement, at a finite place $v$ of $K$ in a quadratic extension $L/K$, that when a scalar $c\cdot 1_2$ is the norm of an element whose $\sigma$-conjugacy class contains no scalar, the split regular elements $\operatorname{diag}(ca, ca^{-1})$ of the same determinant fibre lying close enough to that scalar fail to be norms at all; it is the local input used in the vanishing of unipotent germs for matching automorphic forms in degree two, as in [`AutomorphicForm.germ_unipotent_eq_zero_of_areMatchingLocal_of_forall_germ_of_not_isSigmaConjugate_scalar_of_finrank_eq_two`](thm.html#AutomorphicForm.germ_unipotent_eq_zero_of_areMatchingLocal_of_forall_germ_of_not_isSigmaConjugate_scalar_of_finrank_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_nhds_forall_not_exists_isNormOf_diagonal_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.exists_nhds_forall_not_exists_isNormOf_diagonal_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) :
    ∃ U ∈ nhds (1 : (v.adicCompletion K)), ∀ a : (v.adicCompletion K)ˣ, (a : (v.adicCompletion K)) ∈ U → (a : (v.adicCompletion K)) ^ 2 ≠ 1 →
      ∀ γ : GL (Fin 2) (v.adicCompletion K),
        (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
          !![(c : (v.adicCompletion K)) * (a : (v.adicCompletion K)), 0; 0, (c : (v.adicCompletion K)) * ((a⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K))] →
        ¬ ∃ δ' : GL (Fin 2) (L ⊗[K] v.adicCompletion K), AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ γ δ' := by sorry
