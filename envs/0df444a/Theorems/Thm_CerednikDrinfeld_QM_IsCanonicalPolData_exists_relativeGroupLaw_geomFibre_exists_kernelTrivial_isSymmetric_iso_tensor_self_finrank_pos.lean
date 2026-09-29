-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCanonicalPolData_exists_relativeGroupLaw_geomFibre_exists_kernelTrivial_isSymmetric_iso_tensor_self_finrank_pos
-- name    : CerednikDrinfeld.QM.IsCanonicalPolData.exists_relativeGroupLaw_geomFibre_exists_kernelTrivial_isSymmetric_iso_tensor_self_finrank_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/edfd00d6-7f7a-5705-9549-6f7cfb9ff809
-- title:
--   Canonical polarisation datum is a symmetric square on geometric fibres
-- statement:
--   Let $S$ be a commutative ring, $f : A \to \operatorname{Spec} S$ a morphism of schemes, and $L$ a relative group law on $f$, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} S$. Assume `AbelianSchemePropertyBundle S f`: $f$ is smooth and proper, each set-theoretic fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law; assume moreover that every fibre $f^{-1}(s)$ has topological Krull dimension $2$. Let $I$ be a type, $act : I \to \operatorname{End}(A)$ a family of endomorphisms with $act\,x$ followed by $f$ equal to $f$, $star : I \to I$ an indexing map, and $\mathcal L$ a module on $A$ satisfying `IsCanonicalPolData`: $\mathcal L$ is invertible; it is symmetric, meaning $[-1]^{*}\mathcal L$ and $\mathcal L$ become isomorphic after pullback over some open neighbourhood of each point of $\operatorname{Spec} S$; its Mumford bundle kernel is the $2$-torsion, i.e. for every $R$-point $x$ of $A$ over $t$ the slice of $(\,\mathrm{add}^{*}\mathcal L \otimes \mathrm{pr}_1^{*}\mathcal L^{\vee} \otimes \mathrm{pr}_2^{*}\mathcal L^{\vee})$ at $x$ is locally trivial over the base exactly when $2x = 0$; there is a faithfully flat $S$-algebra $S'$ such that for every relative group law $L'$ on $A_{S'} \to \operatorname{Spec} S'$ whose multiplication is compatible with $L$ under the first projection, $\mathcal L_{S'}$ is locally isomorphic to $\mathcal L_0 \otimes [-1]^{*}\mathcal L_0$ for some invertible $\mathcal L_0$ with trivial Mumford kernel; `Scheme.Modules.geomFibreH0Finrank f 𝓛 k sk` is positive for every algebraically closed field $k$ and ring map $sk : S \to k$; and `RosatiCompatible` holds for $\mathcal L$, $L$, $act$ and $star$. Then for every algebraically closed field $k$ and every ring homomorphism $sk : S \to k$ the geometric fibre $f_k : A \times_S \operatorname{Spec} k \to \operatorname{Spec} k$ carries a relative group law $L_k$ which is commutative, satisfies `AbelianSchemePropertyBundle k` and is smooth of relative dimension $2$, and there is a module $\mathcal L_0$ on $A \times_S \operatorname{Spec} k$ which is invertible, has trivial Mumford kernel for $L_k$ (only the unit point has locally trivial slice), is symmetric for $L_k$, admits an isomorphism from the pullback of $\mathcal L$ along the first projection to $\mathcal L_0 \otimes \mathcal L_0$, and whose global sections form a $k$-vector space (for the algebra structure induced by $f_k$ on global functions) of positive finite rank.
--
--   This is the descent of a canonical polarisation datum on a quaternionic abelian surface over a base $S$ to each geometric fibre, where it becomes the tensor square of a symmetric principal invertible sheaf with nonvanishing $H^0$. It is used in the treatment of fake elliptic curves, notably for the statements that $\mathcal L_0^{\otimes 3}$ and $\mathcal L_0^{\otimes 4}$ give closed immersions by global sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCanonicalPolData_exists_relativeGroupLaw_geomFibre_exists_kernelTrivial_isSymmetric_iso_tensor_self_finrank_pos.lean

import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.IsCanonicalPolData.exists_relativeGroupLaw_geomFibre_exists_kernelTrivial_isSymmetric_iso_tensor_self_finrank_pos
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (hA : AbelianSchemePropertyBundle S f)
    (hdim : ∀ s : ↥(Spec (CommRingCat.of S)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = 2)
    {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f) (star : I → I)
    (𝓛 : A.Modules) (h𝓛 : IsCanonicalPolData f L act act_over star 𝓛)
    (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) :
    ∃ Lk : RelativeGroupLaw k (pullback.snd f (Spec.map (CommRingCat.ofHom sk))),
      Lk.IsCommutative ∧
      AbelianSchemePropertyBundle k (pullback.snd f (Spec.map (CommRingCat.ofHom sk))) ∧
      SmoothOfRelativeDimension 2 (pullback.snd f (Spec.map (CommRingCat.ofHom sk))) ∧
      ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom sk))).Modules,
        Scheme.Modules.IsInvertible 𝓛₀ ∧
        KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom sk))) Lk 𝓛₀ ∧
        IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom sk))) Lk 𝓛₀ ∧
        Nonempty ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj 𝓛 ≅ 𝓛₀ ⊗ 𝓛₀) ∧
        (letI : Algebra k Γ(pullback f (Spec.map (CommRingCat.ofHom sk)), ⊤) :=
           ((Scheme.ΓSpecIso (.of k)).inv ≫ (pullback.snd f (Spec.map (CommRingCat.ofHom sk))).appLE ⊤ ⊤ le_top).hom.toAlgebra
         letI : Module k Γ(𝓛₀, ⊤) := Module.compHom _ (algebraMap k Γ(pullback f (Spec.map (CommRingCat.ofHom sk)), ⊤))
         0 < Module.finrank k Γ(𝓛₀, ⊤)) := by sorry
