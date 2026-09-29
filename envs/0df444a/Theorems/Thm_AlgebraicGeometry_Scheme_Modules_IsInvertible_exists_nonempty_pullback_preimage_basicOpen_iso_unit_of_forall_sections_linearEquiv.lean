-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_nonempty_pullback_preimage_basicOpen_iso_unit_of_forall_sections_linearEquiv
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_nonempty_pullback_preimage_basicOpen_iso_unit_of_forall_sections_linearEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/7c074021-69f6-50b0-884a-cfc504e03220
-- title:
--   Triviality near a trivial fibre of a proper flat family
-- statement:
--   Let $R$ be a Noetherian commutative ring, $Y$ a scheme and $f : Y \to \operatorname{Spec} R$ a proper flat morphism, and let $P$ be a sheaf of modules on $Y$ which is invertible in the sense of the predicate `Scheme.Modules.IsInvertible`: every point of $Y$ has an open neighbourhood $U$ such that the pullback of $P$ along the open immersion $U \hookrightarrow Y$ is isomorphic to the unit sheaf of modules on $U$. Assume, first, that $\Gamma(P, \top)$, regarded as an $R$-module through the algebra map $R \to \Gamma(Y, \top)$ determined by $f$, admits an $R$-linear isomorphism with $R$; and, second, that for every commutative $R$-algebra $C$ in the same universe the global sections of the pullback of $P$ along the first projection $Y \times_{\operatorname{Spec} R} \operatorname{Spec} C \to Y$, viewed as a $C$-module through the algebra map determined by the second projection, admit a $C$-linear isomorphism with $C$. Let $\mathfrak p$ be a prime of $R$ and write $Y_{\kappa(\mathfrak p)} = Y \times_{\operatorname{Spec} R} \operatorname{Spec} \kappa(\mathfrak p)$ for the fibre over the residue field of $\mathfrak p$. Assume that every non-zero global section of the structure sheaf of $Y_{\kappa(\mathfrak p)}$ is a unit, and that the pullback of $P$ to $Y_{\kappa(\mathfrak p)}$ along the first projection is isomorphic to the unit sheaf of modules there. Then there exists $g \in R$ with $g \notin \mathfrak p$ such that the pullback of $P$ along the open immersion $f^{-1}(D(g)) \hookrightarrow Y$ is isomorphic to the unit sheaf of modules on the open subscheme $f^{-1}(D(g))$.
--
--   This is the step in the proof of the see-saw theorem that produces the largest locus over which an invertible sheaf on a proper flat family is a pullback from the base, isolated here over a base on which the direct image of $P$ is universally a line bundle: such a $P$ is trivial over a neighbourhood of every base point with trivial fibre. It is used in the construction of the relative Picard functor, in [`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_ideal_forall_locallyIsoOver_unit_iff_map_eq_bot`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_ideal_forall_locallyIsoOver_unit_iff_map_eq_bot), where the defining ideal of that locus is obtained.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_nonempty_pullback_preimage_basicOpen_iso_unit_of_forall_sections_linearEquiv.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_nonempty_pullback_preimage_basicOpen_iso_unit_of_forall_sections_linearEquiv
    {R : Type u} [CommRing R] [IsNoetherianRing R] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of R))
    [IsProper f] [Flat f] (P : Y.Modules) (hP : Scheme.Modules.IsInvertible P)
    (hsec0 : letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f P ⊤
      Nonempty (Γ(P, ⊤) ≃ₗ[R] R))
    (hsec : ∀ (C : Type u) [CommRing C] [Algebra R C],
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (Limits.pullback.snd f (specMap R C))
        ((Scheme.Modules.pullback (Limits.pullback.fst f (specMap R C))).obj P) ⊤
      Nonempty (Γ((Scheme.Modules.pullback (Limits.pullback.fst f (specMap R C))).obj P, ⊤) ≃ₗ[C] C))
    (𝔭 : PrimeSpectrum R)
    (hO : ∀ t : Γ(Limits.pullback f (specMap R 𝔭.asIdeal.ResidueField), ⊤), t ≠ 0 → IsUnit t)
    (htriv : Nonempty ((Scheme.Modules.pullback
        (Limits.pullback.fst f (specMap R 𝔭.asIdeal.ResidueField))).obj P ≅
      SheafOfModules.unit (Limits.pullback f (specMap R 𝔭.asIdeal.ResidueField)).ringCatSheaf)) :
    ∃ g : R, g ∉ 𝔭.asIdeal ∧
      Nonempty ((Scheme.Modules.pullback (f ⁻¹ᵁ (PrimeSpectrum.basicOpen g)).ι).obj P ≅
        SheafOfModules.unit (↑(f ⁻¹ᵁ (PrimeSpectrum.basicOpen g)) : Scheme.{u}).ringCatSheaf) := by sorry
