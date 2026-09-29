-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_of_d_comap_section_eq_of_forall_preimage_chart
-- name    : AlgebraicGeometry.OModulePresheaf.exists_d_eq_of_d_comap_section_eq_of_forall_preimage_chart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/88f05009-b016-50cb-88d7-39e49832d719
-- title:
--   Čech 1-cocycle bounding on slabs and on a section
-- statement:
--   Let $R$ be a commutative ring, let $X$ and $P$ be schemes, let $\pi_X \colon X \to \operatorname{Spec} R$ be separated, let $p \colon P \to X$ be a morphism such that $p$ followed by $\pi_X$ is separated, and let $s \colon X \to P$ be an affine morphism with $s$ followed by $p$ equal to $\mathrm{id}_X$. Assume that for every affine open $U \subseteq X$ the ring map $\Gamma(X,U) \to \Gamma(P, p^{-1}U)$ induced by $p$ is surjective. Let $\mathcal{W}$ be an ordered affine cover of $P$, i.e. a finite linearly ordered index type $\mathcal{W}.\iota$ together with affine opens $\mathcal{W}.U_i$ whose supremum is $\top$; for a strictly monotone $t \colon \mathrm{Fin}(i+1) \to \mathcal{W}.\iota$ write $\mathcal{W}.\mathrm{inter}\, t = \bigcap_j \mathcal{W}.U_{t(j)}$. Cochains are taken in the $\mathcal{O}$-module presheaf `OModulePresheaf.unit`, which assigns to an open its ring of sections regarded as an $R$-module through the structure morphism, with the presheaf restrictions as restriction maps, and `d` is the alternating Čech differential on strictly monotone index tuples. Let $c$ be a $1$-cochain for $p$ followed by $\pi_X$ on $\mathcal{W}$ with $\mathrm{d}c = 0$. Assume: (i) for every $i \in \mathcal{W}.\iota$ there is a family $\beta$ assigning to each $0$-index $t$ a section over $\mathcal{W}.\mathrm{inter}\, t \cap p^{-1}(s^{-1}\mathcal{W}.U_i)$ such that for every $1$-index $t$ the restriction of $c_t$ to $\mathcal{W}.\mathrm{inter}\, t \cap p^{-1}(s^{-1}\mathcal{W}.U_i)$ equals $\sum_{j \in \mathrm{Fin}\,2} (-1)^j \beta(\mathcal{W}.\mathrm{face}\, t\, j)$ restricted there; (ii) the $1$-cochain on the cover $\mathcal{W}.\mathrm{comap}\, s$ of $X$, with opens $s^{-1}\mathcal{W}.U_i$, obtained from $c$ by applying $s$ on sections and restricting, is the Čech differential of a $0$-cochain. Then there is a $0$-cochain $b$ for $p$ followed by $\pi_X$ on $\mathcal{W}$ with $\mathrm{d}b = c$.
--
--   This is the exactness of the low-degree Leray sequence for the map $p$, made explicit at the level of alternating Čech cochains for a single ordered affine cover, with the splitting supplied by the section $s$: hypothesis (i) says the class of $c$ dies in the $\check H^0$ of the sheaf $U \mapsto \check H^1(\mathcal{W}|_{p^{-1}U})$, while hypothesis (ii) kills the class coming from the base. It feeds the variant [`AlgebraicGeometry.OModulePresheaf.exists_d_eq_of_d_comap_slice_eq_of_bijective_algebraMap`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_d_eq_of_d_comap_slice_eq_of_bijective_algebraMap), and the proof cites the row exactness of the Leray double complex together with the compatibility of its vertical differential with the biaugmentation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_of_d_comap_section_eq_of_forall_preimage_chart.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_d_eq_of_d_comap_section_eq_of_forall_preimage_chart
    {R : Type u} [CommRing R] {X P : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R)) [IsSeparated πX]
    (p : P ⟶ X) [IsSeparated (p ≫ πX)]
    (s : X ⟶ P) [IsAffineHom s] (hs : s ≫ p = 𝟙 X)
    (hp : ∀ U : X.Opens, IsAffineOpen U → Function.Surjective (p.app U).hom)
    (𝒲 : P.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p ≫ πX)).cochain 𝒲 1)
    (hc : (OModulePresheaf.unit (p ≫ πX)).d 𝒲 1 c = 0)
    (hcU : ∀ i : 𝒲.ι, ∃ β : ∀ t : 𝒲.Idx 0, Γ(P, 𝒲.inter t ⊓ p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i)),
      ∀ t : 𝒲.Idx (0 + 1),
        (P.presheaf.map (homOfLE (inf_le_left :
            𝒲.inter t ⊓ p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i) ≤ 𝒲.inter t)).op).hom (c t)
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (P.presheaf.map (homOfLE (inf_le_inf_right (p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i))
                (𝒲.inter_le_inter_face t j))).op).hom (β (𝒲.face t j)))
    (hcs : ∃ b : (OModulePresheaf.unit πX).cochain (𝒲.comap s) 0,
      (OModulePresheaf.unit πX).d (𝒲.comap s) 0 b = fun t =>
        (X.presheaf.map (homOfLE (𝒲.comap_inter_le s t)).op).hom ((s.app (𝒲.inter t)).hom (c t))) :
    ∃ b : (OModulePresheaf.unit (p ≫ πX)).cochain 𝒲 0, (OModulePresheaf.unit (p ≫ πX)).d 𝒲 0 b = c := by sorry
