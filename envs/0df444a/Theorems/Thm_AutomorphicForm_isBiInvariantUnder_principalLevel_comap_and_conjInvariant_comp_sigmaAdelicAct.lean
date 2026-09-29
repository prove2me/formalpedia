-- Prove2me | Theorems.Thm_AutomorphicForm_isBiInvariantUnder_principalLevel_comap_and_conjInvariant_comp_sigmaAdelicAct
-- name    : AutomorphicForm.isBiInvariantUnder_principalLevel_comap_and_conjInvariant_comp_sigmaAdelicAct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/4807d81b-a0f9-5ecf-b384-a87464b27879
-- title:
--   Galois transport of level, conjugation invariance and support of adelic kernels
-- statement:
--   Let $K \subseteq L$ be number fields, let $D$ be an idelic Galois descent datum for $L/K$ (a homomorphism from $\mathrm{Aut}_K(L)$ to the ring automorphisms of $\mathbb{A}_L$, each continuous and compatible with the action on principal adeles), let $\sigma \in \mathrm{Aut}_K(L)$, let $M$ be an ideal of $\mathcal{O}_L$ and let $g : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$. Write $U(M)$ for the intersection of `principalLevel (𝓞 L) L M`, the meet of the preimage under `glFin` of the level-$M$ congruence subgroup of $\mathrm{GL}_2$ of the finite adeles with its conjugate by the Weyl element $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, and of the kernel of `glArch`, the elements whose archimedean component is trivial. Assume: $g(ux) = g(x) = g(xu)$ for all $u \in U(M)$ and all $x$; $g(\iota(\kappa)\, x\, \iota(\kappa)^{-1}) = g(x)$ for every infinite place $w$ of $L$, every $\kappa$ in `rowIsometrySubgroup₀ w.Completion` with $\iota =$ `rowIsometryInclAt₀ L w` and all $x$; and $g(x) \neq 0$ only if the finite component `glFin` of $x$ equals that of some element of $U(M)$. Then $g \circ$ `sigmaAdelicAct K L D σ`, the composite of $g$ with the entrywise action of $D.\mathrm{act}\,\sigma$ on $\mathrm{GL}_2(\mathbb{A}_L)$, satisfies the same three assertions with $M$ replaced by its preimage $\sigma^{-1}M$ under the ring automorphism of $\mathcal{O}_L$ induced by $\sigma$.
--
--   This records the stability, under the twisting operator attached to $\sigma$, of the class of conjugation-invariant kernels that are bi-invariant under and supported on a principal congruence subgroup of $\mathrm{GL}_2(\mathbb{A}_L)$: the level is transported from $M$ to $\sigma^{-1}M$ while the archimedean conjugation invariance and the support condition persist. It is used in the estimate [`AutomorphicForm.forall_isCompact_exists_tsum_norm_finsum_twistedConvOp_mul_conj_le_of_orthonormal_of_isFundamentalDomain_slab`](thm.html#AutomorphicForm.forall_isCompact_exists_tsum_norm_finsum_twistedConvOp_mul_conj_le_of_orthonormal_of_isFundamentalDomain_slab) for the $\sigma$-twisted kernel.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isBiInvariantUnder_principalLevel_comap_and_conjInvariant_comp_sigmaAdelicAct.lean

import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_PlaceTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel
open IsDedekindDomain

theorem AutomorphicForm.isBiInvariantUnder_principalLevel_comap_and_conjInvariant_comp_sigmaAdelicAct
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (M : Ideal (𝓞 L)) (g : AdelicGL2 (𝓞 L) L → ℂ)
    (hgU : IsBiInvariantUnder L (principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) g)
    (hgconj : ∀ (w : InfinitePlace L) (κ : rowIsometrySubgroup₀ w.Completion) (x : AdelicGL2 (𝓞 L) L),
      g (rowIsometryInclAt₀ L w κ * x * (rowIsometryInclAt₀ L w κ)⁻¹) = g x)
    (hgsupp : ∀ x : AdelicGL2 (𝓞 L) L, g x ≠ 0 →
      ∃ u ∈ principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L, glFin (𝓞 L) L u = glFin (𝓞 L) L x) :
    IsBiInvariantUnder L
        (principalLevel (𝓞 L) L
            (M.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L)) ⊓
          finiteAdelicGL2Subgroup L)
        (g ∘ sigmaAdelicAct K L D σ) ∧
    (∀ (w : InfinitePlace L) (κ : rowIsometrySubgroup₀ w.Completion) (x : AdelicGL2 (𝓞 L) L),
      (g ∘ sigmaAdelicAct K L D σ) (rowIsometryInclAt₀ L w κ * x * (rowIsometryInclAt₀ L w κ)⁻¹) =
        (g ∘ sigmaAdelicAct K L D σ) x) ∧
    (∀ x : AdelicGL2 (𝓞 L) L, (g ∘ sigmaAdelicAct K L D σ) x ≠ 0 →
      ∃ u ∈ principalLevel (𝓞 L) L
            (M.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L)) ⊓
          finiteAdelicGL2Subgroup L,
        glFin (𝓞 L) L u = glFin (𝓞 L) L x) := by sorry
