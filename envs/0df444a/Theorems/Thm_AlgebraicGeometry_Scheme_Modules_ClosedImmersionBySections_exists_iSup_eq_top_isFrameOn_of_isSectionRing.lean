-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_exists_iSup_eq_top_isFrameOn_of_isSectionRing
-- name    : AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections.exists_iSup_eq_top_isFrameOn_of_isSectionRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/6feefed0-f2dc-58c3-9d7a-65424f00295a
-- title:
--   Degree-one frames on a finite open cover of X
-- statement:
--   Let $S$ be a commutative ring, $X$ a scheme, $f : X \to \operatorname{Spec} S$ a morphism, and $L$ an object of `X.Modules`. Let $R$ be a commutative $S$-algebra with an $\mathbb{N}$-grading given by $S$-submodules $\mathcal{R}_n \subseteq R$, and let $\iota_n : \mathcal{R}_n \to \Gamma(L^{\otimes n}, \top)$ be maps into the global sections of the tensor powers $L^{\otimes 0} = \mathbf{1}$, $L^{\otimes (n+1)} = L^{\otimes n} \otimes L$. Assume `IsSectionRing` holds for $(f, L, R, \mathcal{R}, \iota)$: each $\iota_n$ is bijective and additive, $\iota_n(s \cdot x) = \beta(s) \cdot \iota_n(x)$ where $\beta(s) \in \Gamma(X, \top)$ is the image of $s \in S$ under $f$ on global sections, $\iota_0(1)$ is the unit section of $\mathbf{1}$, and $\iota_{m+n}(xy)$ is the tensor product section $\iota_m(x) \otimes \iota_n(y)$ read through the canonical isomorphism $L^{\otimes m} \otimes L^{\otimes n} \cong L^{\otimes (m+n)}$. Assume also `ClosedImmersionBySections L f`: there are an $N$ and a `ProjPresentation` of $L$ along $f$ of rank $N+1$ — global sections $\sigma_i \in \Gamma(L, \top)$, a morphism $\mathrm{toProj} : X \to \operatorname{Proj} S[x_0, \dots, x_N]$ over $\operatorname{Spec} S$, each $\sigma_i$ framing $L$ on $\mathrm{toProj}^{-1} D_+(x_i)$, and the ratio compatibilities between the $\sigma_i$ — whose morphism $\mathrm{toProj}$ is a closed immersion. The conclusion: there exist $N \in \mathbb{N}$, elements $\tau_i \in \mathcal{R}_1$ and opens $V_i \subseteq X$ indexed by $i \in \{0, \dots, N\}$ such that $\bigsqcup_i V_i = \top$ and, for each $i$, $\iota_1(\tau_i) \in \Gamma(L^{\otimes 1}, \top)$ is a frame on $V_i$, i.e. for every open $W \le V_i$ the map $\Gamma(X, W) \to \Gamma(L^{\otimes 1}, W)$, $g \mapsto g \cdot \iota_1(\tau_i)|_W$, is bijective.
--
--   This produces, from a presentation of $L$ exhibiting $X$ as a closed subscheme of a projective space over $S$, a finite open cover of $X$ on which degree-one elements of the graded section ring $R$ trivialise $L$. It feeds the construction of the canonical morphism to $\operatorname{Proj} R$, being cited by [`AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_isCanonicalToProj`](thm.html#AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_isCanonicalToProj).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_exists_iSup_eq_top_isFrameOn_of_isSectionRing.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization

theorem AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections.exists_iSup_eq_top_isFrameOn_of_isSectionRing
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (hva : Scheme.Modules.ClosedImmersionBySections L f) :
    ∃ (N : ℕ) (τ : Fin (N + 1) → 𝓡 1) (V : Fin (N + 1) → X.Opens),
      (⨆ i, V i) = ⊤ ∧ ∀ i, AlgebraicGeometry.Scheme.Modules.IsFrameOn (ι 1 (τ i)) (V i) := by sorry
