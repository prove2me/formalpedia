-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame_of_frame_pullback
-- name    : AlgebraicGeometry.Scheme.Modules.exists_basicOpen_forall_exists_frame_of_frame_pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/bf14c1f3-a748-51a3-b04b-8d06259d565c
-- title:
--   Frames spread from the K-fibre to a basic open over 𝔭
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme and $f\colon X\to\operatorname{Spec}R$ a universally closed morphism. Let $M$ be a module over the structure sheaf of $X$ which is invertible in the sense of `Scheme.Modules.IsInvertible`, i.e. every point of $X$ has an open neighbourhood $U$ such that the pullback of $M$ along the inclusion $U\hookrightarrow X$ is isomorphic to the unit sheaf of modules on $U$. Let $\iota$ be a finite index type and $m\colon\iota\to\Gamma(M,\top)$ a family of global sections of $M$. Let $K$ be a field with an $R$-algebra structure whose structure map has kernel exactly $\mathfrak p.\mathrm{asIdeal}$, for a prime $\mathfrak p$ of $R$, and form the fibre product $X_K$ of $f$ with $\operatorname{Spec}$ of $R\to K$, with first projection $p\colon X_K\to X$. Assume that for every point $z$ of $X_K$ there are an index $i$ and an open $U'\ni z$ such that for every open $V'\le U'$ the map $\Gamma(X_K,V')\to\Gamma(p^{*}M,V')$ sending $g$ to $g$ times the restriction to $V'$ of the image of $m_i$ under the unit of the pullback–pushforward adjunction for $p$ is bijective. The conclusion is that there exists $g\in R$ with $g\notin\mathfrak p.\mathrm{asIdeal}$ such that for every $x\in X$ with $f(x)\in D(g)$ there are an index $i$ and an open $U\ni x$ with the property that for every open $V\le U$ the map $\Gamma(X,V)\to\Gamma(M,V)$, $g\mapsto g\cdot m_i|_V$, is bijective.
--
--   This is the spreading-out step for invertible modules: the property that one of finitely many given global sections frames $M$ (trivialises it locally, in the sense that multiplication by it is an isomorphism onto $M$ on small opens) passes from the geometric fibre $X_K$ over $\mathfrak p$ to the preimage of a basic open neighbourhood $D(g)$ of $\mathfrak p$, using only universal closedness of $f$ and no cohomology. It feeds the construction of trivialisations of line bundles over basic opens in the relative Picard functor setup, and is cited by the results producing bijective multiplication maps over preimages of basic opens, isomorphisms of pullbacks with the unit sheaf, and finiteness by sections of tensor powers from geometric-fibre hypotheses.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame_of_frame_pullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_basicOpen_forall_exists_frame_of_frame_pullback
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [UniversallyClosed f]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) {ι : Type*} [Finite ι] (m : ι → Γ(M, ⊤))
    (K : Type u) [Field K] [Algebra R K] (𝔭 : PrimeSpectrum R) (h𝔭 : RingHom.ker (algebraMap R K) = 𝔭.asIdeal)
    (hgen : ∀ z : ↑(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      ∃ (i : ι) (U' : (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).Opens), z ∈ U' ∧
        ∀ V' : (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).Opens, V' ≤ U' →
          Function.Bijective fun g : Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))), V') =>
            g • (((Scheme.Modules.pullback
                    (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj M).presheaf.map
                  (homOfLE (le_top : V' ≤ ⊤)).op
              ((((Scheme.Modules.pullbackPushforwardAdjunction
                  (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).unit.app M).app ⊤) (m i)) :
              Γ((Scheme.Modules.pullback
                    (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj M, V'))) :
    ∃ g : R, g ∉ 𝔭.asIdeal ∧ ∀ x : X, f x ∈ PrimeSpectrum.basicOpen g →
      ∃ (i : ι) (U : X.Opens), x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
        Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (m i) : Γ(M, V)) := by sorry
