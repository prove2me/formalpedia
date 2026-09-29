-- Prove2me | Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_ringHom_smul_map_pow_eq
-- name    : AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_ringHom_smul_map_pow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/45ac6d39-2767-5eea-86d2-93b66477376a
-- title:
--   Dehomogenisation at a degree-one frame of a section ring
-- statement:
--   Let $S$ be a commutative ring, $X$ a scheme, $f : X \to \operatorname{Spec} S$ a morphism, and $L$ an object of `X.Modules`. Let $R$ be a commutative ring that is an $S$-algebra, let $\mathcal R_\bullet : \mathbb N \to \mathrm{Submodule}\,S\,R$ be a graded $S$-algebra structure on $R$, and let $\iota_n : \mathcal R_n \to \Gamma(L^{\otimes n}, \top)$ be maps into the global sections of the tensor powers $L^{\otimes n}$ (defined by $L^{\otimes 0} = \mathbf 1$, $L^{\otimes (n+1)} = L^{\otimes n} \otimes L$). Assume `IsSectionRing f L R 𝓡 ι`, that is: each $\iota_n$ is bijective and additive; $\iota_n(s \cdot x) = \mathrm{baseScalar}(f)(s) \cdot \iota_n(x)$ for $s \in S$, where $\mathrm{baseScalar}(f)(s) \in \Gamma(X,\top)$ is the image of $s$ under $f$ on global sections; $\iota_0(1)$ is the section $1$ of the monoidal unit; and $\iota_{m+n}(xy)$ is the image of the tensor product section $\iota_m(x) \otimes \iota_n(y)$ under the isomorphism $L^{\otimes m} \otimes L^{\otimes n} \cong L^{\otimes (m+n)}$. Let $\tau \in \mathcal R_1$ and let $V \subseteq X$ be open such that $\iota_1(\tau)$ is a frame on $V$, meaning that for every open $W \le V$ the map $\Gamma(X,W) \to \Gamma(L,W)$, $g \mapsto g \cdot \iota_1(\tau)|_W$, is bijective. Then there is a ring homomorphism $\varphi : R \to \Gamma(X,V)$ such that: $\varphi(\mathrm{algebraMap}_{S,R}(a))$ is the restriction to $V$ of $\mathrm{baseScalar}(f)(a)$ for every $a \in S$; for every $m$ the section $\iota_{m \cdot 1}(\tau^m)$ is a frame on $V$ (degrees being written $m \cdot 1$); and for every $m$ and every $s \in \mathcal R_{m \cdot 1}$ one has $\varphi(s) \cdot \iota_{m \cdot 1}(\tau^m)|_V = \iota_{m \cdot 1}(s)|_V$ in $\Gamma(L^{\otimes (m\cdot 1)}, V)$.
--
--   This is the dehomogenisation map attached to a degree-one element $\tau$ of a section ring: on the locus where $\iota_1(\tau)$ trivialises $L$, taking the ratio of a homogeneous section against the corresponding power of $\tau$ produces a ring homomorphism from the whole of $R$ to the functions on that chart, compatible with the structure morphism to $\operatorname{Spec} S$. It is used in the construction of the canonical morphism to $\operatorname{Proj}$ of a section ring, being cited by [`AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_isCanonicalToProj`](thm.html#AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_isCanonicalToProj) and by [`AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.exists_smul_map_pow_eq_map_of_section`](thm.html#AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.exists_smul_map_pow_eq_map_of_section).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_ringHom_smul_map_pow_eq.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization

theorem AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_ringHom_smul_map_pow_eq
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (τ : 𝓡 1) (V : X.Opens) (hτ : AlgebraicGeometry.Scheme.Modules.IsFrameOn (ι 1 τ) V) :
    ∃ φ : R →+* Γ(X, V),
      (∀ a : S, φ (algebraMap S R a) =
        X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (AlgebraicGeometry.GradedOAlgebra.baseScalar f a)) ∧
      (∀ m : ℕ, AlgebraicGeometry.Scheme.Modules.IsFrameOn
        (ι (m • 1) ⟨(τ : R) ^ m, SetLike.pow_mem_graded m τ.2⟩) V) ∧
      (∀ (m : ℕ) (s : 𝓡 (m • 1)),
        φ (s : R) • (L.tensorPow (m • 1)).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
            (ι (m • 1) ⟨(τ : R) ^ m, SetLike.pow_mem_graded m τ.2⟩) =
          (L.tensorPow (m • 1)).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (ι (m • 1) s)) := by sorry
