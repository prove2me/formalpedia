-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_mem_preimage_le_of_directed_subalgebra
-- name    : AlgebraicGeometry.Scheme.exists_mem_preimage_le_of_directed_subalgebra
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/7eb272ac-41b7-53ba-b653-f475f83dd672
-- title:
--   Opens of X_A descend to a finite stage of a directed union
-- statement:
--   Let $R$ and $A$ be commutative rings with $A$ an $R$-algebra, and let $S : \iota \to$ `Subalgebra R A` be a family of $R$-subalgebras of $A$ which is directed for the order $\le$ (any two members are dominated by a third) and exhausts $A$, in the sense that every $a \in A$ lies in some $S_i$. Let $X$ be a scheme and $f : X \to \operatorname{Spec} R$ a morphism of schemes. For each $i$ write $X_A$ for the pullback of $f$ along $\operatorname{Spec}$ of the structure map $R \to A$ and $X_{S_i}$ for the pullback of $f$ along $\operatorname{Spec}$ of $R \to S_i$, and suppose given morphisms $q_i : X_A \to X_{S_i}$ which are compatible with both projections: $q_i$ followed by the first projection $X_{S_i} \to X$ is the first projection $X_A \to X$, and $q_i$ followed by the second projection $X_{S_i} \to \operatorname{Spec} S_i$ equals the second projection $X_A \to \operatorname{Spec} A$ followed by $\operatorname{Spec}$ of the inclusion $S_i \hookrightarrow A$. Then for every open subset $U$ of $X_A$ and every point $w \in U$ there exist an index $i$ and an open subset $W$ of $X_{S_i}$ such that $w \in q_i^{-1}(W)$ and $q_i^{-1}(W) \le U$.
--
--   This is the topological statement that $X_A$ is the limit of the schemes $X_{S_i}$ along a directed union $A = \bigcup_i S_i$ of $R$-subalgebras: the preimages $q_i^{-1}(W)$ of opens from the finite stages form a basis of the topology of $X_A$. It is the input to [`AlgebraicGeometry.isClosedMap_pullback_snd_of_directed_subalgebra`](thm.html#AlgebraicGeometry.isClosedMap_pullback_snd_of_directed_subalgebra), which deduces closedness of the projection $X_A \to \operatorname{Spec} A$ from its analogues over the subalgebras, en route to the affine criteria for universal closedness and the valuative criterion over discrete valuation rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_mem_preimage_le_of_directed_subalgebra.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_mem_preimage_le_of_directed_subalgebra
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type v} (S : ι → Subalgebra R A) (hdir : Directed (· ≤ ·) S) (hS : ∀ a : A, ∃ i, a ∈ S i)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (q : ∀ i, pullback f (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap R ↥(S i)))))
    (hq₁ : ∀ i, q i ≫ pullback.fst f _ = pullback.fst f _)
    (hq₂ : ∀ i, q i ≫ pullback.snd f _ =
      pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥(S i) A)))
    (U : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R A)))).Opens)
    (w : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R A))))) (hw : w ∈ U) :
    ∃ (i : ι) (W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R ↥(S i))))).Opens),
      w ∈ (q i) ⁻¹ᵁ W ∧ (q i) ⁻¹ᵁ W ≤ U := by sorry
