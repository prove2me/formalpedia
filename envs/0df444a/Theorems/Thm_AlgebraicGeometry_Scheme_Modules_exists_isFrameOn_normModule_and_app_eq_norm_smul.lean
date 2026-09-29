-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_normModule_and_app_eq_norm_smul
-- name    : AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_normModule_and_app_eq_norm_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/69f6f8ae-e54f-5fa6-8020-ef078ec56616
-- title:
--   Norm module frame: N_π(ι')(1) is Nm(g) times a frame
-- statement:
--   Let $\pi\colon X'\to X$ be a morphism of schemes and $d$ a natural number, and suppose the map `normModuleUnitEval` $\pi$ $d$ — the internal-hom evaluation $\det_d(\pi_*\mathcal O_{X'})\otimes(\det_d(\pi_*\mathcal O_{X'}))^{\vee}\to\mathbf 1$ on $X$, where $(-)^\vee$ is the internal hom into the unit module and $\det_d$ the $d$-th exterior power — is an isomorphism. Let $P$ be an $\mathcal O_{X'}$-module, $\iota'\colon\mathbf 1\to P$ a morphism from the unit module, $U$ an open of $X$, and $e\colon \mathrm{Fin}\,d\to\Gamma(\pi_*\mathbf 1,U)$ a family such that for every open $W\le U$ there is a $\Gamma(X,W)$-basis of $\Gamma(\pi_*\mathbf 1,W)$ indexed by $\mathrm{Fin}\,d$ whose $i$-th member is the restriction of $e_i$. Let $s\in\Gamma(P,\pi^{-1}U)$ be a frame on $\pi^{-1}U$, i.e. for every open $W\le\pi^{-1}U$ the map $h\mapsto h\cdot(s|_W)$ from $\Gamma(X',W)$ to $\Gamma(P,W)$ is bijective, and let $g\in\Gamma(X',\pi^{-1}U)$ satisfy $\iota'_{\pi^{-1}U}(1)=g\cdot s$, where $1$ is the unit section of $\mathbf 1$. Give $\Gamma(X',\pi^{-1}U)$ the $\Gamma(X,U)$-algebra structure coming from $\pi^{\sharp}$ on $U$. Then there exists $\Omega\in\Gamma(\det_d(\pi_*P)\otimes(\det_d(\pi_*\mathbf 1))^{\vee},U)$ which is a frame on $U$ in the same sense, such that the composite of the inverse of `normModuleUnitEval` $\pi$ $d$ with the image of $\iota'$ under the functor $L\mapsto\det_d(\pi_*L)\otimes(\det_d(\pi_*\mathbf 1))^{\vee}$, evaluated on $U$ at the unit section $1$, equals $\mathrm{Nm}_{\Gamma(X',\pi^{-1}U)/\Gamma(X,U)}(g)\cdot\Omega$.
--
--   This is the local computation underlying the norm construction for modules along a morphism that is finite locally free of rank $d$: in a frame of $P$ on $\pi^{-1}U$ adapted to a basis $e_1,\dots,e_d$ of $\pi_*\mathcal O_{X'}$ over $U$, the induced section of the norm module has local equation the algebra norm of the local equation of the given section. It is used in the construction of the isomorphism recorded by `nonempty_normModule_invModule_ker_iso`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_normModule_and_app_eq_norm_smul.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_normModule_and_app_eq_norm_smul
    {X X' : Scheme.{u}} (π : X' ⟶ X) (d : ℕ) [IsIso (Scheme.Modules.normModuleUnitEval π d)]
    {P : X'.Modules} (ι' : 𝟙_ X'.Modules ⟶ P) (U : X.Opens)
    (e : Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules), U))
    (he : ∀ (W : X.Opens) (hW : W ≤ U),
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules), W),
        ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules)).presheaf.map (homOfLE hW).op (e i))
    (s : Γ(P, π ⁻¹ᵁ U)) (hs : Scheme.Modules.IsFrameOn s (π ⁻¹ᵁ U))
    (g : Γ(X', π ⁻¹ᵁ U)) (hg : ι'.app (π ⁻¹ᵁ U) (Scheme.Modules.toUnitSection _ 1) = g • s) :
    letI : Algebra Γ(X, U) Γ(X', π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra
    ∃ Ω : Γ(Scheme.Modules.normModule π d P, U), Scheme.Modules.IsFrameOn Ω U ∧
      (inv (Scheme.Modules.normModuleUnitEval π d) ≫ (Scheme.Modules.normModuleFunctor π d).map ι').app U
          (Scheme.Modules.toUnitSection U 1) = (Algebra.norm Γ(X, U) g) • Ω := by sorry
