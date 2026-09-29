-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_unit_hom_pullback_ne_zero_of_isIso_and_tensor
-- name    : AlgebraicGeometry.Scheme.Modules.exists_unit_hom_pullback_ne_zero_of_isIso_and_tensor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/ae11f592-4b2f-59e0-b88a-000632883623
-- title:
--   Non-zero unit sections under base change and pull-back along an automorphism
-- statement:
--   Let $k$ be a field, $A$ a scheme, $f : A \to \operatorname{Spec} k$ a morphism, and $N : A \to A$ an endomorphism which is an isomorphism and satisfies $f \circ N = f$ (written $N \gg f = f$). Let $\mathcal L, \mathcal M$ be objects of the monoidal category $A.\mathrm{Modules}$ of modules on $A$, let $k'$ be a field and $s_k : k \to k'$ a ring homomorphism. Put $A' := A \times_{\operatorname{Spec} k} \operatorname{Spec} k'$, the categorical pullback of $f$ along $\operatorname{Spec}(s_k)$, with first projection $p_1 : A' \to A$. The assertion is a conjunction of two implications between statements of the form 'there exists a non-zero morphism from the monoidal unit $\mathbb 1$ of $A'.\mathrm{Modules}$ to the given object': first, if $p_1^{*}\mathcal M$ admits a non-zero morphism from $\mathbb 1$, then so does $p_1^{*}(N^{*}\mathcal M)$; second, if the tensor product $p_1^{*}\mathcal L \otimes p_1^{*}(N^{*}\mathcal M)$ admits a non-zero morphism from $\mathbb 1$, then so does $p_1^{*}(\mathcal L \otimes N^{*}\mathcal M)$. Only the two implications are claimed, not any isomorphism of the corresponding groups of morphisms.
--
--   A coherence statement comparing pull-back along a base-changed automorphism with pull-back along the projection of a fibre product, and pull-back with the tensor product; it transports non-vanishing of a section from one object to another. It is used in the positivity argument [`AlgebraicGeometry.Polarisation.geomFibreH0Finrank_tensor_pullback_negMor_pos`](thm.html#AlgebraicGeometry.Polarisation.geomFibreH0Finrank_tensor_pullback_negMor_pos), where $N$ is the inversion morphism of an abelian scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_unit_hom_pullback_ne_zero_of_isIso_and_tensor.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.exists_unit_hom_pullback_ne_zero_of_isIso_and_tensor
    (k : Type u) [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k))
    (N : A ⟶ A) (hN : N ≫ f = f) [IsIso N]
    (𝓛 𝓜 : A.Modules) (k' : Type u) [Field k'] (sk : k →+* k') :
    ((∃ s : 𝟙_ (Limits.pullback f (Spec.map (CommRingCat.ofHom sk))).Modules ⟶
          (Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj 𝓜, s ≠ 0) →
      ∃ t : 𝟙_ (Limits.pullback f (Spec.map (CommRingCat.ofHom sk))).Modules ⟶
          (Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj
            ((Scheme.Modules.pullback N).obj 𝓜), t ≠ 0) ∧
    ((∃ u : 𝟙_ (Limits.pullback f (Spec.map (CommRingCat.ofHom sk))).Modules ⟶
          (Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj 𝓛 ⊗
            (Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj
              ((Scheme.Modules.pullback N).obj 𝓜), u ≠ 0) →
      ∃ v : 𝟙_ (Limits.pullback f (Spec.map (CommRingCat.ofHom sk))).Modules ⟶
          (Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj
            (𝓛 ⊗ (Scheme.Modules.pullback N).obj 𝓜), v ≠ 0) := by sorry
