-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_sameDivisorScheme
-- name    : AlgebraicGeometry.RelEffCartierDiv.exists_sameDivisorScheme
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/4f929d68-db4a-5c4d-b832-7935e7ab7836
-- title:
--   Same-divisor relation on the fibre power: finite flat of rank r!
-- statement:
--   Let $f \colon \mathcal{C} \to S$ be a morphism of schemes which is separated and smooth of relative dimension $1$, and let $r$ be a natural number. Write $X =$ `fibrePowOver f r` for the wide pullback of $r$ copies of $f$, i.e. the $r$-fold fibre power $\mathcal{C} \times_S \cdots \times_S \mathcal{C}$, with projections `fibrePowOver.proj f r i` for $i \in \mathrm{Fin}\,r$ and structure morphism `fibrePowOver.toBase f r` to $S$. The assertion is that there exist a scheme $R$ and two morphisms $s, t \colon R \to X$ which agree after composition with `fibrePowOver.toBase f r`, such that: the induced morphism $R \to X \times_S X$ obtained from $s$, $t$ and that agreement is a closed immersion; each of $s$ and $t$ is finite, flat, locally of finite presentation and surjective, with `finrank` equal to $r!$ at every point; and, for every scheme $T'$ and every pair $u, v \colon T' \to X$ agreeing after composition with `fibrePowOver.toBase f r`, there is a morphism $w \colon T' \to R$ with $w \gg s = u$ and $w \gg t = v$ if and only if `SameDivisor` holds for the two $r$-tuples $(u \text{ followed by } \mathrm{pr}_i)_i$ and $(v \text{ followed by } \mathrm{pr}_i)_i$ of morphisms $T' \to \mathcal{C}$ over $S$, that is, if and only if the two products $\prod_i \ker \Gamma_{a_i}$ of graph ideal sheaf data on $\mathcal{C} \times_S T'$ coincide. No uniqueness of $w$ is claimed.
--
--   This exhibits "having the same associated divisor" as a closed, finite locally free relation $R \rightrightarrows \mathcal{C}^r_S$ of rank $r!$ on the $r$-fold fibre power, described by its functor of points; it is the input for constructing the divisor scheme $\mathrm{Div}^r_{\mathcal{C}/S}$ as a quotient by a finite flat equivalence relation. It is used by [`AlgebraicGeometry.RelEffCartierDiv.exists_isUniversal_of_isAffine`](thm.html#AlgebraicGeometry.RelEffCartierDiv.exists_isUniversal_of_isAffine).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_exists_sameDivisorScheme.lean

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.exists_sameDivisorScheme
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] [SmoothOfRelativeDimension 1 f] (r : ℕ) :
    ∃ (R : Scheme.{u}) (s t : R ⟶ fibrePowOver f r)
      (hst : s ≫ fibrePowOver.toBase f r = t ≫ fibrePowOver.toBase f r),
      IsClosedImmersion (pullback.lift s t hst) ∧
      (IsFinite s ∧ Flat s ∧ LocallyOfFinitePresentation s ∧ Surjective s ∧
        ∀ x, s.finrank x = r.factorial) ∧
      (IsFinite t ∧ Flat t ∧ LocallyOfFinitePresentation t ∧ Surjective t ∧
        ∀ x, t.finrank x = r.factorial) ∧
      ∀ ⦃T' : Scheme.{u}⦄ (u v : T' ⟶ fibrePowOver f r)
        (huv : u ≫ fibrePowOver.toBase f r = v ≫ fibrePowOver.toBase f r),
        (∃ w : T' ⟶ R, w ≫ s = u ∧ w ≫ t = v) ↔
          SameDivisor f (fun i => u ≫ fibrePowOver.proj f r i)
            (fun i => by rw [Category.assoc, fibrePowOver.proj_comp])
            (fun i => v ≫ fibrePowOver.proj f r i)
            (fun i => by rw [Category.assoc, fibrePowOver.proj_comp, huv]) := by sorry
