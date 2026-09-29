-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_existsUnique_ihomEval_eq
-- name    : AlgebraicGeometry.Scheme.Modules.IsFrameOn.existsUnique_ihomEval_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/22cf8df1-68dd-5d33-bf40-4956657ff8e2
-- title:
--   Sections of Hom(P,Q) are determined by their value on a frame
-- statement:
--   Let $X$ be a scheme, let $P$ and $Q$ be sheaves of $\mathcal O_X$-modules on $X$ (objects of `X.Modules`), let $V$ be an open subset of $X$ and let $p \in \Gamma(P, V)$. Assume `Scheme.Modules.IsFrameOn p V`, that is: for every open $W$ with $W \le V$ (the inclusion being used both as $W \le V$ and as the index bound in the definition), the map $\Gamma(X, W) \to \Gamma(P, W)$, $g \mapsto g \cdot (p|_W)$, where $p|_W$ is the image of $p$ under the restriction map of the presheaf of $P$, is bijective. Then for every $q \in \Gamma(Q, V)$ there is exactly one section $\theta \in \Gamma((\mathrm{ihom}\,P)(Q), V)$ of the internal Hom sheaf over $V$ with $\mathrm{ihomEval}\,P\,Q\,V\,p\,\theta = q$; here `Scheme.Modules.ihomEval` is the evaluation obtained by transporting $\theta$ along the additive equivalence identifying sections of the internal Hom over $V$ with natural families of linear maps indexed by morphisms out of $\mathrm{op}\,V$, taking the component at the identity of $\mathrm{op}\,V$, and applying it to $p$.
--
--   This is the statement that a frame (a section generating the module freely on every smaller open) presents $\mathcal P|_V$ as a free rank-one module, so that $\mathcal{H}om_{\mathcal O_X}(\mathcal P, \mathcal Q)(V) \to \mathcal Q(V)$, $\theta \mapsto \theta(p)$, is a bijection. It is used in the treatment of invertible sheaves and rigidified line bundles, for instance to produce isomorphisms of modules from matching frames and to compare an invertible module with the tensor unit.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_existsUnique_ihomEval_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesIhomSections

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsFrameOn.existsUnique_ihomEval_eq
    {X : Scheme.{u}} {P Q : X.Modules} {V : X.Opens} {p : Γ(P, V)}
    (hp : Scheme.Modules.IsFrameOn p V) (q : Γ(Q, V)) :
    ∃! θ : Γ((ihom P).obj Q, V), Scheme.Modules.ihomEval P Q V p θ = q := by sorry
