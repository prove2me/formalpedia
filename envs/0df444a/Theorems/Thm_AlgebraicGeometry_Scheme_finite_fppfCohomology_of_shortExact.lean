-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_finite_fppfCohomology_of_shortExact
-- name    : AlgebraicGeometry.Scheme.finite_fppfCohomology_of_shortExact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/030251fe-6891-54e6-bec2-ab1b8e1919bc
-- title:
--   Finiteness of fppf cohomology in the middle of an extension
-- statement:
--   Let $S$ be a scheme (in universe $u$). The small fppf site of $S$ has underlying category `S.Fppf`, the category of objects over $S$ whose structure morphism is flat and locally of finite presentation, equipped with the small Grothendieck topology `smallFppfTopology S` attached to that morphism property; for an abelian sheaf $F$ on this site (valued in `Ab.{u+1}`) the group $H^n_{\mathrm{fppf}}(S,F)$ is Mathlib's sheaf cohomology `F.H n`, written `fppfCohomology S F n`. The theorem takes a short complex $X$ of such sheaves, say $X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3$ with $g \circ f = 0$, together with the hypothesis that $X$ is short exact in the abelian category of abelian sheaves on the small fppf site of $S$ (that is, $f$ is a monomorphism, $g$ an epimorphism, and the complex exact in the middle), a natural number $n$, and the hypotheses that the types $H^n_{\mathrm{fppf}}(S,X_1)$ and $H^n_{\mathrm{fppf}}(S,X_3)$ are finite. The conclusion is that $H^n_{\mathrm{fppf}}(S,X_2)$ is finite. No hypothesis is imposed on $S$ or on the sheaves beyond short exactness.
--
--   This is the two-out-of-three finiteness statement (middle term) read off the long exact cohomology sequence of a short exact sequence of abelian sheaves on the small fppf site, the standard dévissage step used when bounding fppf cohomology of finite flat group schemes. It is used by [`AlgebraicGeometry.Scheme.finite_fppfCohomology_of_shortExact_chain`](thm.html#AlgebraicGeometry.Scheme.finite_fppfCohomology_of_shortExact_chain), which iterates it along a filtration.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_finite_fppfCohomology_of_shortExact.lean

import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory
universe u

theorem AlgebraicGeometry.Scheme.finite_fppfCohomology_of_shortExact
    (S : Scheme.{u}) {X : ShortComplex (Sheaf (smallFppfTopology S) Ab.{u + 1})}
    (hX : X.ShortExact) (n : ℕ)
    (h₁ : Finite (fppfCohomology S X.X₁ n)) (h₃ : Finite (fppfCohomology S X.X₃ n)) :
    Finite (fppfCohomology S X.X₂ n) := by sorry
