-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_biCech_preimageFamily_equiv_tensor_cochain_pinned
-- name    : AlgebraicGeometry.OModulePresheaf.exists_biCech_preimageFamily_equiv_tensor_cochain_pinned
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/1ea55e50-ce88-5b81-8fcd-906d90e62b65
-- title:
--   Bi-Čech complex of X×_k Y as a tensor double complex
-- statement:
--   Let $k$ be a field and let $\pi_X \colon X \to \operatorname{Spec} k$, $\pi_Y \colon Y \to \operatorname{Spec} k$ be separated morphisms of schemes, and let $\mathfrak U$, $\mathfrak V$ be ordered affine covers of $X$ and of $Y$, that is, finite linearly ordered index sets together with affine opens whose supremum is $\top$. Write $P = X \times_{\operatorname{Spec} k} Y$ with projections $p_1, p_2$, and let $\mathfrak A = p_1^{-1}\mathfrak U$, $\mathfrak B = p_2^{-1}\mathfrak V$ be the resulting ordered open families on $P$ (same index sets, opens $p_1^{-1}\mathfrak U_i$, $p_2^{-1}\mathfrak V_j$). The assertion is the existence of $k$-linear isomorphisms $e_{p,q}$, for all $p,q \in \mathbb N$, from the bidegree-$(p,q)$ term `BiCech.C` of the bi-Čech double complex of the $\mathcal O$-module presheaf `unit` on $P$ relative to $p_1$ followed by $\pi_X$ (the presheaf $U \mapsto \Gamma(P,U)$ with its $k$-algebra and restriction structure) for the families $\mathfrak A, \mathfrak B$, onto $\check C^p(\mathfrak U;\mathcal O_X) \otimes_k \check C^q(\mathfrak V;\mathcal O_Y)$, where $\check C^p(\mathfrak U;\mathcal O_X)$ is the product over strictly monotone $(p+1)$-tuples $s$ of $\Gamma(X, \bigsqcap_j \mathfrak U_{s_j})$, subject to three conditions: $e$ carries the horizontal differential `BiCech.dH` to $d_{\mathfrak U} \otimes \mathrm{id}$ and the vertical differential `BiCech.dV` to $\mathrm{id} \otimes d_{\mathfrak V}$ (with $d$ the Čech differential), with no sign twist; and $e_{p,q}$ is pinned on pure tensors, in that for cochains $\alpha$, $\beta$ and indices $s$, $t$ the component of $e_{p,q}^{-1}(\alpha \otimes_k \beta)$ at $(s,t)$, a section over $\bigsqcap_j p_1^{-1}\mathfrak U_{s_j} \sqcap \bigsqcap_j p_2^{-1}\mathfrak V_{t_j}$, is the product of the pullback of $\alpha_s$ along $p_1$ and the pullback of $\beta_t$ along $p_2$, both restricted to that open.
--
--   This is the chain-level Künneth comparison for the structure sheaf: the bi-Čech double complex of $\mathcal O$ on the product of the two pullback ("strip") families of $X \times_k Y$ is identified, compatibly with both differentials and with an explicit formula on pure tensors, with the tensor product over $k$ of the two Čech complexes; the affine input is the identification $\Gamma(U \times_k V, \mathcal O) \cong \Gamma(X,U) \otimes_k \Gamma(Y,V)$ for affine opens, supplied by [`AlgebraicGeometry.Scheme.Pullback.isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage`](thm.html#AlgebraicGeometry.Scheme.Pullback.isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage). It feeds the passage to total complexes and cup products in [`AlgebraicGeometry.OModulePresheaf.exists_HTot_biCech_equiv_prodCover_cup_pinned`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_HTot_biCech_equiv_prodCover_cup_pinned) and the injectivity statement [`AlgebraicGeometry.OModulePresheaf.kunneth_toModule_diag_injective_of_cls_unitPullback`](thm.html#AlgebraicGeometry.OModulePresheaf.kunneth_toModule_diag_injective_of_cls_unitPullback).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_biCech_preimageFamily_equiv_tensor_cochain_pinned.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BiCech
import Definitions.Def_AlgebraicGeometry_BoundedCochainTensor
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TensorProduct AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_biCech_preimageFamily_equiv_tensor_cochain_pinned
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of k)) (πY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated πX] [IsSeparated πY]
    (𝔘 : X.OrderedAffineCover) (𝔙 : Y.OrderedAffineCover) :
    ∃ e : ∀ p q : ℕ,
        OModulePresheaf.BiCech.C (OModulePresheaf.unit (pullback.fst πX πY ≫ πX))
            (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY)) p q ≃ₗ[k]
          ((OModulePresheaf.unit πX).cochain 𝔘 p ⊗[k] (OModulePresheaf.unit πY).cochain 𝔙 q),

      (∀ (p q : ℕ) (c : OModulePresheaf.BiCech.C (OModulePresheaf.unit (pullback.fst πX πY ≫ πX))
            (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY)) p q),
        e (p + 1) q (OModulePresheaf.BiCech.dH (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)) _ _ p q c) =
          ((OModulePresheaf.unit πX).d 𝔘 p).rTensor _ (e p q c)) ∧
      (∀ (p q : ℕ) (c : OModulePresheaf.BiCech.C (OModulePresheaf.unit (pullback.fst πX πY ≫ πX))
            (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY)) p q),
        e p (q + 1) (OModulePresheaf.BiCech.dV (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)) _ _ p q c) =
          ((OModulePresheaf.unit πY).d 𝔙 q).lTensor _ (e p q c)) ∧

      (∀ (p q : ℕ) (α : (OModulePresheaf.unit πX).cochain 𝔘 p) (β : (OModulePresheaf.unit πY).cochain 𝔙 q)
          (s : 𝔘.Idx p) (t : 𝔙.Idx q),
        (e p q).symm (α ⊗ₜ[k] β) (s, t) =
          ((pullback πX πY).presheaf.map (homOfLE (inf_le_left.trans
              (le_of_eq (Scheme.OrderedAffineCover.preimage_iInf_fin (pullback.fst πX πY) (fun j => 𝔘.U (s.1 j))).symm))).op).hom
            (((pullback.fst πX πY).app (𝔘.inter s)).hom (α s)) *
          ((pullback πX πY).presheaf.map (homOfLE (inf_le_right.trans
              (le_of_eq (Scheme.OrderedAffineCover.preimage_iInf_fin (pullback.snd πX πY) (fun j => 𝔙.U (t.1 j))).symm))).op).hom
            (((pullback.snd πX πY).app (𝔙.inter t)).hom (β t))) := by sorry
