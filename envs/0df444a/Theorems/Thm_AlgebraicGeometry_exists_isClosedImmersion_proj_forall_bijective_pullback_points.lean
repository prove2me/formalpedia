-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_proj_forall_bijective_pullback_points
-- name    : AlgebraicGeometry.exists_isClosedImmersion_proj_forall_bijective_pullback_points
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/6517e784-075a-58d2-94e7-8e2f5f384a41
-- title:
--   Projective ambient scheme with Hilb×(P^N)^k points
-- statement:
--   Let $\mathrm{Hilb}$ be a scheme with a morphism $p : \mathrm{Hilb} \to \operatorname{Spec}\mathbb Z$, let $N' \in \mathbb N$, and let $\iota_H : \mathrm{Hilb} \to \operatorname{Proj}$ of the graded ring of polynomials in $N'+1$ variables over $\mathbb Z$ (i.e. $\mathbb P^{N'}_{\mathbb Z}$) be a closed immersion with $\iota_H$ followed by the structure morphism `ProjSpace.π ℤ N'` equal to $p$. Let $B$ be a commutative ring and $N, k \in \mathbb N$. The assertion is that there exist a scheme $W_0$, a morphism $\pi_W : W_0 \to \operatorname{Spec} B$, a natural number $M$, a closed immersion $j_W : W_0 \to \mathbb P^M_B$ with $j_W$ followed by `ProjSpace.π B M` equal to $\pi_W$, a morphism $\mathrm{pr}_H : W_0 \to \mathrm{Hilb}$, and morphisms $\mathrm{pr}_i : W_0 \to \mathbb P^N_B$ for $i \in \mathrm{Fin}\,k$, each satisfying $\mathrm{pr}_i$ followed by `ProjSpace.π B N` equal to $\pi_W$, such that for every commutative ring $R$ that is a $B$-algebra the map
--   $$s \longmapsto \bigl(\mathrm{pr}_H \circ s,\ (\mathrm{pr}_i \circ s)_{i}\bigr)$$
--   from the set of morphisms $s : \operatorname{Spec} R \to W_0$ with $\pi_W \circ s$ equal to the morphism $\operatorname{Spec} R \to \operatorname{Spec} B$ induced by $B \to R$, to the set of pairs consisting of a morphism $\operatorname{Spec} R \to \mathrm{Hilb}$ together with a $k$-tuple of morphisms $\operatorname{Spec} R \to \mathbb P^N_B$ each lying over $\operatorname{Spec} R \to \operatorname{Spec} B$, is bijective. No compatibility of the $\mathrm{Hilb}$-component with $p$ is imposed on the target side.
--
--   This provides the ambient space for an embedded moduli problem: $W_0$ plays the role of $\mathrm{Hilb}_B \times_{\operatorname{Spec} B} (\mathbb P^N_B)^k$, realised as a closed subscheme of a projective space over $B$ whose $R$-points, for any $B$-algebra $R$, are exactly the expected tuples. It is used in the construction of an embedded representing object for framed polarised abelian schemes over a Noetherian base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isClosedImmersion_proj_forall_bijective_pullback_points.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_isClosedImmersion_proj_forall_bijective_pullback_points
    (Hilb : Scheme.{0}) (p : Hilb ⟶ Spec (CommRingCat.of ℤ)) (N' : ℕ)
    (ιH : Hilb ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) ℤ))
    (hιH : IsClosedImmersion ιH) (hιHp : ιH ≫ ProjSpace.π ℤ N' = p)
    (B : Type) [CommRing B] (N k : ℕ) :
    ∃ (W₀ : Scheme.{0}) (πW : W₀ ⟶ Spec (CommRingCat.of B)) (M : ℕ)
      (jW : W₀ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (M + 1)) B))
      (_ : IsClosedImmersion jW) (_ : jW ≫ ProjSpace.π B M = πW)
      (prH : W₀ ⟶ Hilb)
      (prY : Fin k → (W₀ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B)))
      (hprY : ∀ i, prY i ≫ ProjSpace.π B N = πW),
      ∀ (R : Type) [CommRing R] [Algebra B R],
        Function.Bijective
          (fun s : {s : Spec (CommRingCat.of R) ⟶ W₀ // s ≫ πW = Spec.map (CommRingCat.ofHom (algebraMap B R))} =>
            (⟨(s.1 ≫ prH, fun i => s.1 ≫ prY i), fun i => by
                rw [Category.assoc, hprY i, s.2]⟩ :
              {y : (Spec (CommRingCat.of R) ⟶ Hilb) ×
                  (Fin k → (Spec (CommRingCat.of R) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B))) //
                ∀ i, y.2 i ≫ ProjSpace.π B N = Spec.map (CommRingCat.ofHom (algebraMap B R))})) := by sorry
