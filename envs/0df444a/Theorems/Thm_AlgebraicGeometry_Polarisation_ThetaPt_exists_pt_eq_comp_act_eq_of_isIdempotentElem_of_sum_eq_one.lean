-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_exists_pt_eq_comp_act_eq_of_isIdempotentElem_of_sum_eq_one
-- name    : AlgebraicGeometry.Polarisation.ThetaPt.exists_pt_eq_comp_act_eq_of_isIdempotentElem_of_sum_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/4a7a6fd9-1f5f-529d-987b-53c6f0d16b2d
-- title:
--   Gluing theta points along a complete orthogonal family of idempotents
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme, $f : A \to \operatorname{Spec} S$ a morphism carrying a relative group law $L$ (a functorial group structure on the sets of $t$-points $\{\varphi : T \to A \mid \varphi \circ f = t\}$, natural in the test morphism $t$), and $\mathcal L$ an $\mathcal O_A$-module. Let $R$ be a commutative ring, $t : \operatorname{Spec} R \to \operatorname{Spec} S$, and let $\varepsilon_1,\dots,\varepsilon_m \in R$ be idempotents with $\sum_j \varepsilon_j = 1$ and $\varepsilon_j\varepsilon_l = 0$ for $j \neq l$. Write $R_j := \operatorname{Localization.Away}(\varepsilon_j)$, $t_j := \operatorname{Spec}(R \to R_j)$ followed by $t$, and let $b_j : A \times_{\operatorname{Spec} S} \operatorname{Spec} R_j \to A \times_{\operatorname{Spec} S} \operatorname{Spec} R$ be morphisms compatible with the two projections in the sense that $b_j$ followed by the first projection is the first projection, and $b_j$ followed by the second projection is the second projection followed by $\operatorname{Spec}(R \to R_j)$; these conditions determine $b_j$ as the morphism induced on fibre products. Let $c_j$ be arbitrary isomorphisms $b_j^{*}\,\mathrm{pr}_A^{*}\mathcal L \cong \mathrm{pr}_A^{*}\mathcal L$ over $\operatorname{Spec} R_j$, and for each $j$ let $\theta'_j$ be a theta point over $t_j$, that is, a $t_j$-point $\mathrm{pt}$ of $A$ together with an isomorphism between the pullback of $\mathrm{pr}_A^{*}\mathcal L$ along the translation by $\mathrm{pt}$ and $\mathrm{pr}_A^{*}\mathcal L$, the resulting operator on global sections being written $\mathrm{act}$. The assertion is that there exists a theta point $\theta$ over $t$ such that: for every $j$ the underlying morphism of $\theta'_j.\mathrm{pt}$ equals $\operatorname{Spec}(R \to R_j)$ followed by that of $\theta.\mathrm{pt}$; for every $j$ and every global section $s$ of $\mathrm{pr}_A^{*}\mathcal L$ over $A \times_{\operatorname{Spec} S}\operatorname{Spec} R$, the operator $\theta'_j.\mathrm{act}$ applied to $c_j(b_j^{*}s)$ equals $c_j(b_j^{*}(\theta.\mathrm{act}\, s))$; and for all global sections $s, s'$, if for every $j$ the operator $\theta'_j.\mathrm{act}$ sends $c_j(b_j^{*}s)$ to $c_j(b_j^{*}s')$, then $\theta.\mathrm{act}\, s = s'$.
--
--   This is the Zariski (indeed clopen) sheaf property of the theta-group functor $R \mapsto \mathcal G(\mathcal L)(R)$ with respect to the decomposition $\operatorname{Spec} R = \coprod_j \operatorname{Spec} R[1/\varepsilon_j]$ determined by a finite complete orthogonal family of idempotents: theta points over the pieces glue to a theta point over $R$, compatibly with the translation operators, and the last clause records that the glued operator is determined by its restrictions. It is used in the construction of Schrödinger frames for polarised abelian schemes and in the assembly of level structures from those on the pieces of a cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_ThetaPt_exists_pt_eq_comp_act_eq_of_isIdempotentElem_of_sum_eq_one.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.Polarisation.ThetaPt.exists_pt_eq_comp_act_eq_of_isIdempotentElem_of_sum_eq_one
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (𝓛 : A.Modules) {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    {m : ℕ} (ε : Fin m → R) (hε : ∀ j, IsIdempotentElem (ε j)) (hsum : ∑ j, ε j = 1)
    (horth : ∀ j l, j ≠ l → ε j * ε l = 0)
    (b : ∀ j, pullback f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t) ⟶ pullback f t)
    (hb₁ : ∀ j, b j ≫ pullback.fst f t =
      pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t))
    (hb₂ : ∀ j, b j ≫ pullback.snd f t =
      pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))))
    (c : ∀ j, (Scheme.Modules.pullback (b j)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) ≅
      (Scheme.Modules.pullback
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t))).obj 𝓛)
    (θ' : ∀ j, ThetaPt f L 𝓛 (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t)) :
    ∃ θ : ThetaPt f L 𝓛 t,
      (∀ j, (θ' j).pt.1 = Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ θ.pt.1) ∧
      (∀ j (s : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤)),
        (θ' j).act ((c j).hom.app ⊤ (Scheme.Modules.pullbackLocalSection (b j) s :
            Γ((Scheme.Modules.pullback (b j)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤))) =
          (c j).hom.app ⊤ (Scheme.Modules.pullbackLocalSection (b j) (θ.act s) :
            Γ((Scheme.Modules.pullback (b j)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤))) ∧
      (∀ s s' : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤),
        (∀ j, (θ' j).act ((c j).hom.app ⊤ (Scheme.Modules.pullbackLocalSection (b j) s :
            Γ((Scheme.Modules.pullback (b j)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤))) =
          (c j).hom.app ⊤ (Scheme.Modules.pullbackLocalSection (b j) s' :
            Γ((Scheme.Modules.pullback (b j)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤))) →
        θ.act s = s') := by sorry
