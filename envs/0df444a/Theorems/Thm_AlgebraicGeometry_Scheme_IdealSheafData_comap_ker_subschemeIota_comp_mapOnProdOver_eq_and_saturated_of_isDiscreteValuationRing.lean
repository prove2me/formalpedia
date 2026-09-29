-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ker_subschemeIota_comp_mapOnProdOver_eq_and_saturated_of_isDiscreteValuationRing
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.comap_ker_subschemeIota_comp_mapOnProdOver_eq_and_saturated_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/39a3a80b-220a-5d34-bf8a-e1dd31b408f4
-- title:
--   Kernel of the closure of a generic-fibre subscheme over a DVR
-- statement:
--   Let $f \colon \mathcal C \to S$ be a morphism of schemes, let $O$ be a discrete valuation ring which is a domain, and let $g \colon \operatorname{Spec} O \to S$ be an $S$-point. Let $T'$ be a field equipped with an $O$-algebra structure making it a fraction field of $O$, and let $gT \colon \operatorname{Spec} T' \to S$ be a morphism with $\operatorname{Spec}$ of the structure map $O \to T'$ followed by $g$ equal to $gT$. Write $\iota$ for `mapOnProdOver f (Spec.map (CommRingCat.ofHom (algebraMap O T'))) hψ`, the morphism $\mathcal C \times_S \operatorname{Spec} T' \to \mathcal C \times_S \operatorname{Spec} O$ obtained from the identity on $\mathcal C$, the map $\operatorname{Spec} T' \to \operatorname{Spec} O$ and the identity on $S$. Let $I$ be a quasi-coherent ideal sheaf datum on $\mathcal C \times_S \operatorname{Spec} T'$, and let $J$ be the kernel ideal sheaf of the closed immersion $I.\mathtt{subschemeι}$ followed by $\iota$. The assertion is twofold: first, the comap of $J$ along $\iota$ equals $I$; second, for every irreducible $\varpi \in O$, every affine open $U$ of $\mathcal C \times_S \operatorname{Spec} O$ and every $s \in \Gamma(\mathcal C \times_S \operatorname{Spec} O, U)$, if the restriction to $U$ of the global section obtained by pulling $\varpi$ back along the second projection times $s$ lies in $J(U)$, then $s$ lies in $J(U)$.
--
--   This describes the scheme-theoretic closure, in $\mathcal C \times_S \operatorname{Spec} O$, of a closed subscheme of the generic fibre $\mathcal C \times_S \operatorname{Spec} T'$: its ideal restricts back to the given ideal on the generic fibre, and it is $\varpi$-saturated, i.e. the structure sheaf of the closure has no $\varpi$-torsion. It feeds the construction of relative effective Cartier divisors over a discrete valuation ring and, through that, the divisor-theoretic work on the modular curve model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ker_subschemeIota_comp_mapOnProdOver_eq_and_saturated_of_isDiscreteValuationRing.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.comap_ker_subschemeIota_comp_mapOnProdOver_eq_and_saturated_of_isDiscreteValuationRing
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S}
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (g : Spec (CommRingCat.of O) ⟶ S)
    (T' : Type u) [Field T'] [Algebra O T'] [IsFractionRing O T']
    {gT : Spec (CommRingCat.of T') ⟶ S} (hψ : Spec.map (CommRingCat.ofHom (algebraMap O T')) ≫ g = gT)
    (I : (pullback f gT).IdealSheafData) :
    ((I.subschemeι ≫ mapOnProdOver f (Spec.map (CommRingCat.ofHom (algebraMap O T'))) hψ).ker).comap
        (mapOnProdOver f (Spec.map (CommRingCat.ofHom (algebraMap O T'))) hψ) = I ∧
      ∀ (ϖ : O), Irreducible ϖ → ∀ (U : (pullback f g).affineOpens) (s : Γ(pullback f g, U)),
        (pullback f g).presheaf.map (homOfLE (le_top : (U : (pullback f g).Opens) ≤ ⊤)).op
            ((pullback.snd f g).appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ)) * s ∈
            (I.subschemeι ≫ mapOnProdOver f (Spec.map (CommRingCat.ofHom (algebraMap O T'))) hψ).ker.ideal U →
          s ∈ (I.subschemeι ≫ mapOnProdOver f (Spec.map (CommRingCat.ofHom (algebraMap O T'))) hψ).ker.ideal U := by sorry
