-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_isFrameOn_dual
-- name    : AlgebraicGeometry.Scheme.Modules.IsFrameOn.exists_isFrameOn_dual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/40ab6bb6-4e9a-5d8c-acda-f6283b3c7484
-- title:
--   Existence of a dual frame on V pairing to 1
-- statement:
--   Let $X$ be a scheme, let $P$ be a sheaf of $\mathcal O_X$-modules on $X$, let $U, V$ be open subsets of $X$, and let $p \in \Gamma(P, U)$. Assume `Scheme.Modules.IsFrameOn p V`, that is: for every open $W$ with $W \le U$ and $W \le V$, the map $\Gamma(X, W) \to \Gamma(P, W)$, $g \mapsto g \cdot (p|_W)$, is bijective; and assume $V \le U$. Then there exists a section $q \in \Gamma(\mathrm{dual}\,P, V)$ of the dual module $\mathrm{dual}\,P = \underline{\mathrm{Hom}}(P, \mathbf 1)$, where $\mathbf 1 = \mathbb 1_{X.\mathrm{Modules}}$ is the unit object for the tensor product, with the following two properties. First, `Scheme.Modules.IsFrameOn q V`: for every open $W \le V$ the map $\Gamma(X, W) \to \Gamma(\mathrm{dual}\,P, W)$, $g \mapsto g \cdot (q|_W)$, is bijective. Second, the sections-level evaluation pairing `Scheme.Modules.ihomEval` of $q$ against the restriction $p|_V$ along $V \le U$ equals `Scheme.Modules.unitSection V`, the section of the unit module over $V$ given by $1 \in \Gamma(X, V)$. Here sections of the internal Hom over $V$ are natural families of linear maps over the opens refining $V$, and `ihomEval` applies such a family at the identity.
--
--   This is the statement that a local frame (local generator with trivial annihilator, in the form of bijectivity of multiplication) for $P$ on $V$ produces a dual frame for $\mathcal Hom(P, \mathcal O_X)$ on $V$, normalised to pair to $1$ with the given frame. It feeds the construction of frames for invertible modules and norm modules, and hence the treatment of frame kits for closed immersions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_isFrameOn_dual.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesNormModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.Modules.IsFrameOn.exists_isFrameOn_dual
    {X : Scheme.{u}} {P : X.Modules} {U V : X.Opens} {p : Γ(P, U)}
    (hp : Scheme.Modules.IsFrameOn p V) (hVU : V ≤ U) :
    ∃ q : Γ(Scheme.Modules.dual P, V), Scheme.Modules.IsFrameOn q V ∧
      Scheme.Modules.ihomEval P (𝟙_ X.Modules) V (P.presheaf.map (homOfLE hVU).op p) q =
        Scheme.Modules.unitSection V := by sorry
