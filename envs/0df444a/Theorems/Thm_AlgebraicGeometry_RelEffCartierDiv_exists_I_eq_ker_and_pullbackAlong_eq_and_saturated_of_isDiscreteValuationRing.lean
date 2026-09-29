-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_ker_and_pullbackAlong_eq_and_saturated_of_isDiscreteValuationRing
-- name    : AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_ker_and_pullbackAlong_eq_and_saturated_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/72754ef7-1c46-5333-a85a-a445727c110b
-- title:
--   Schematic closure over a DVR of a relative divisor on the generic fibre
-- statement:
--   Let $f\colon\mathcal C\to S$ be a proper morphism of schemes, let $O$ be a discrete valuation domain with an $S$-point $g\colon\operatorname{Spec} O\to S$, let $T'$ be a field that is a fraction field of $O$, and let $gT\colon\operatorname{Spec} T'\to S$ be obtained by composing $\psi=\operatorname{Spec}(O\to T')$ with $g$, as recorded by the hypothesis $\psi\circ\,\cdot\,$, i.e. $\psi$ followed by $g$ equals $gT$. Let $r$ be a natural number and let $E$ be a relative effective Cartier divisor of degree $r$ for $f$ over $gT$: an ideal sheaf datum $E.I$ on $\mathcal C\times_S\operatorname{Spec} T'$ whose closed subscheme inclusion followed by the second projection is finite, flat and locally of finite presentation, with fibrewise rank $r$ at every point of $\operatorname{Spec} T'$. Then there exists a relative effective Cartier divisor $\bar E$ of degree $r$ for $f$ over $g$ (so on $\mathcal C\times_S\operatorname{Spec} O$, again finite, flat, locally of finite presentation of rank $r$ over $\operatorname{Spec} O$) such that: $\bar E.I$ is the kernel ideal sheaf datum of the closed immersion of $E$ composed with the base-change map $\mathcal C\times_S\operatorname{Spec} T'\to\mathcal C\times_S\operatorname{Spec} O$; the pullback of $\bar E$ along $\psi$, defined by taking the comap of $\bar E.I$ along that same map, equals $E$; and for every irreducible $\varpi\in O$, every affine open $U$ of $\mathcal C\times_S\operatorname{Spec} O$ and every $s\in\Gamma(U)$, if the product of $s$ with the restriction to $U$ of the global function pulled back from $\varpi$ along the projection to $\operatorname{Spec} O$ lies in $\bar E.I(U)$, then $s\in\bar E.I(U)$.
--
--   This is the existence of the schematic closure of a relative divisor on the generic fibre: $\bar E$ is the closed subscheme of the model $\mathcal C\times_S\operatorname{Spec} O$ cut out by the kernel ideal, it is again finite flat of the same degree over $\operatorname{Spec} O$, it restricts to $E$ on the generic fibre, and its ideal is saturated with respect to a uniformiser (equivalently, the structure sheaf of $\bar E$ is torsion-free over $O$). It is used in the study of divisors on the modular curve $X_1(p)$, where the closure of a divisor on the generic fibre is compared with an invertible ideal sheaf.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_ker_and_pullbackAlong_eq_and_saturated_of_isDiscreteValuationRing.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_ker_and_pullbackAlong_eq_and_saturated_of_isDiscreteValuationRing
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsProper f]
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (g : Spec (CommRingCat.of O) ⟶ S)
    (T' : Type u) [Field T'] [Algebra O T'] [IsFractionRing O T']
    {gT : Spec (CommRingCat.of T') ⟶ S} (hψ : Spec.map (CommRingCat.ofHom (algebraMap O T')) ≫ g = gT)
    {r : ℕ} (E : RelEffCartierDiv f r gT) :
    ∃ Ebar : RelEffCartierDiv f r g,
      Ebar.I = (E.I.subschemeι ≫ mapOnProdOver f (Spec.map (CommRingCat.ofHom (algebraMap O T'))) hψ).ker ∧
      Ebar.pullbackAlong (Spec.map (CommRingCat.ofHom (algebraMap O T'))) hψ = E ∧
      ∀ (ϖ : O), Irreducible ϖ → ∀ (U : (pullback f g).affineOpens) (s : Γ(pullback f g, U)),
        (pullback f g).presheaf.map (homOfLE (le_top : (U : (pullback f g).Opens) ≤ ⊤)).op
            ((pullback.snd f g).appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ)) * s ∈ Ebar.I.ideal U →
          s ∈ Ebar.I.ideal U := by sorry
