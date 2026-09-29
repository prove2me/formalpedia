-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_hom_tensorUnit_app_eq_smul
-- name    : AlgebraicGeometry.Scheme.Modules.exists_hom_tensorUnit_app_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/901314d4-c91d-5d09-bb9c-d70a955f9395
-- title:
--   Multiplication by a global function on the unit module
-- statement:
--   Let $X$ be a scheme and let $r \in \Gamma(X, \top)$ be a global section of its structure sheaf. Then there is an endomorphism $t$ of the monoidal unit $\mathbb{1}$ of the category `X.Modules` of sheaves of modules on $X$ (that is, of the structure sheaf viewed as a module over itself) with the following two properties. First, for every open $U$ of $X$ and every section $m \in \Gamma(\mathbb{1}, U)$, the component $t$.app $U$ sends $m$ to $(\,r|_U) \cdot m$, where $r|_U$ denotes the image of $r$ under the restriction map `X.presheaf.map` along the inclusion $U \le \top$, and the product is the module action of $\Gamma(X, U)$ on $\Gamma(\mathbb{1}, U)$. Second, on the total space the component $t$.app $\top$ sends `Scheme.Modules.toUnitSection ⊤ 1`, i.e. the element $1 \in \Gamma(X, \top)$ regarded as a section of the unit module, to $r \cdot$ `Scheme.Modules.toUnitSection ⊤ 1`. The second clause is the case $U = \top$ of the first, recorded separately in the form in which it is used.
--
--   This is the elementary half of the canonical identification $\operatorname{Hom}_{\mathcal{O}_X}(\mathcal{O}_X, M) \cong \Gamma(X, M)$, in the case $M = \mathcal{O}_X$: a global function gives the endomorphism "multiplication by $r$" of the structure sheaf. It is used in the construction of trivialisations and degree-zero twists on resolved models of modular curves, where a global function has to be converted into a morphism out of the unit module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_hom_tensorUnit_app_eq_smul.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.Modules.exists_hom_tensorUnit_app_eq_smul
    {X : Scheme.{u}} (r : Γ(X, ⊤)) :
    ∃ t : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules,
      (∀ (U : X.Opens) (m : Γ(𝟙_ X.Modules, U)),
        t.app U m = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op r • m) ∧
      t.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = r • Scheme.Modules.toUnitSection ⊤ 1 := by sorry
