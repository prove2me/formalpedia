-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_bijective_smul_of_le_preimage_basicOpen_of_forall_isMaximal
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_bijective_smul_of_le_preimage_basicOpen_of_forall_isMaximal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/b11ea610-030a-5ac1-a88a-190cc17d906d
-- title:
--   Seesaw: local framing of a fibrewise trivially invertible sheaf
-- statement:
--   Let $R$ be a commutative ring that is Noetherian, reduced and Jacobson, let $Y$ be a scheme and let $f \colon Y \to \operatorname{Spec} R$ be a proper flat morphism. Assume that for every prime $\mathfrak p$ of $R$ the structure map of the fibre is bijective, in the following sense: the global sections $\Gamma(Y \times_{\operatorname{Spec} R} \operatorname{Spec} \kappa(\mathfrak p), \top)$, regarded as a $\kappa(\mathfrak p)$-algebra via the second projection, receive the algebra map from the residue field $\kappa(\mathfrak p) = \operatorname{Frac}(R/\mathfrak p)$ bijectively. Let $L$ be a sheaf of modules on $Y$ which is invertible in the sense that every point of $Y$ has an open neighbourhood $U$ for which the pull-back of $L$ along $U \hookrightarrow Y$ is isomorphic to the unit sheaf of modules of $U$, and assume that for every maximal ideal $\mathfrak m$ of $R$ the pull-back of $L$ along the first projection $Y \times_{\operatorname{Spec} R} \operatorname{Spec} \kappa(\mathfrak m) \to Y$ is isomorphic to the unit sheaf of modules of that fibre. Then for every prime $\mathfrak p$ of $R$ there exist $g \in R$ with $g \notin \mathfrak p$ and a global section $m \in \Gamma(L, \top)$ such that for every open $V \subseteq f^{-1}(D(g))$ of $Y$ the map $\Gamma(Y, V) \to \Gamma(L, V)$, $a \mapsto a \cdot (m|_V)$, is bijective.
--
--   This is the first half of the seesaw principle in its essential case of an affine base: an invertible sheaf on a proper flat family whose fibres have only constant global functions, trivial on the fibres over the closed points of the base, is framed by a single global section over a basic open neighbourhood of any given point of the base, so that its restriction there is isomorphic to the structure sheaf. It feeds the statement that such a sheaf becomes trivial after pull-back along the second projection of the base change, [`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_nonempty_pullback_baseChangeSnd_iso_unit_of_forall_point`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_nonempty_pullback_baseChangeSnd_iso_unit_of_forall_point), in the construction of the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_bijective_smul_of_le_preimage_basicOpen_of_forall_isMaximal.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_bijective_smul_of_le_preimage_basicOpen_of_forall_isMaximal
    {R : Type u} [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R] [IsJacobsonRing R] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of R)) [IsProper f] [Flat f]
    (hO : ∀ 𝔭 : PrimeSpectrum R,
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField)) ⊤
      Function.Bijective (algebraMap 𝔭.asIdeal.ResidueField
        Γ(Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField), ⊤)))
    (L : Y.Modules) (hL : Scheme.Modules.IsInvertible L)
    (htriv : ∀ 𝔪 : PrimeSpectrum R, 𝔪.asIdeal.IsMaximal →
      Nonempty ((Scheme.Modules.pullback
        (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R 𝔪.asIdeal.ResidueField))).obj L ≅
        SheafOfModules.unit
          (Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R 𝔪.asIdeal.ResidueField)).ringCatSheaf))
    (𝔭 : PrimeSpectrum R) :
    ∃ (g : R) (m : Γ(L, ⊤)), g ∉ 𝔭.asIdeal ∧ ∀ V : Y.Opens, V ≤ f ⁻¹ᵁ (PrimeSpectrum.basicOpen g) →
      Function.Bijective fun a : Γ(Y, V) =>
        a • (L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op m : Γ(L, V)) := by sorry
