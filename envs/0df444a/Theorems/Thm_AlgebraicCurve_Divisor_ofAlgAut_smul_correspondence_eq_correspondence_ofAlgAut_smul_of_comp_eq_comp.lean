-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_ofAlgAut_smul_correspondence_eq_correspondence_ofAlgAut_smul_of_comp_eq_comp
-- name    : AlgebraicCurve.Divisor.ofAlgAut_smul_correspondence_eq_correspondence_ofAlgAut_smul_of_comp_eq_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/30ec6061-195c-55fd-adb7-83a5c180eb99
-- title:
--   Conjugating a correspondence by cross-intertwining automorphisms transposes it
-- statement:
--   Let $K$ be a field and let $F$, $F'$ be fields equipped with $K$-algebra structures, each satisfying `HasPrincipalDivisors` over $K$, i.e. every nonzero element of the field admits a divisor whose coefficient at each place is the order of that element there and whose degree is $0$; here a place of $F$ over $K$ is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself and a principal ideal ring, and a divisor is a finitely supported $\mathbb{Z}$-valued function on places. Let $\varphi, \psi : F \to F'$ be $K$-algebra homomorphisms whose underlying ring homomorphisms are integral, let $g$ be a $K$-algebra automorphism of $F'$ and let $s, t$ be $K$-algebra automorphisms of $F$ satisfying the two intertwining relations $g \circ \psi = \varphi \circ s$ and $g \circ \varphi = \psi \circ t$. Then for every divisor $D$ of $F$ over $K$, the divisor obtained by letting $s$ act on $\psi_*\varphi^* D$, the action being through the semilinear automorphism $(s, \mathrm{id}_K)$ of the pair $(F, K)$, equals $\varphi_*\psi^*$ applied to the translate of $D$ by $t$. The legs of the correspondence are thus exchanged, at the cost of replacing $s$ upstairs by $t$ downstairs.
--
--   This is the divisor-level compatibility of a correspondence with an Atkin–Lehner-type automorphism of the upper field: conjugation by a pair of automorphisms satisfying the two cross-relations turns a correspondence into its transpose. It is used in the analysis of the supports of correspondences under such automorphisms and, on modular curves, to compare the two Hecke correspondences attached to a pair of maps up to a permutation of places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_ofAlgAut_smul_correspondence_eq_correspondence_ofAlgAut_smul_of_comp_eq_comp.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.ofAlgAut_smul_correspondence_eq_correspondence_ofAlgAut_smul_of_comp_eq_comp
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F] [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (g : F' ≃ₐ[K] F') (s t : F ≃ₐ[K] F)
    (h1 : (g : F' →ₐ[K] F').comp ψ = φ.comp (s : F →ₐ[K] F))
    (h2 : (g : F' →ₐ[K] F').comp φ = ψ.comp (t : F →ₐ[K] F))
    (D : Divisor K F) :
    SemilinearAut.ofAlgAut s • Divisor.correspondence φ ψ hφ hψ D =
      Divisor.correspondence ψ φ hψ hφ (SemilinearAut.ofAlgAut t • D) := by sorry
