-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_shortExact_of_app_injective_of_locallySurjective_of_locallyExact
-- name    : AlgebraicGeometry.Scheme.Modules.shortExact_of_app_injective_of_locallySurjective_of_locallyExact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/81c51e42-3599-531b-a9d4-51272f6f177d
-- title:
--   Short exactness of mathcal O_X-module complexes from local data
-- statement:
--   Let $X$ be a scheme and let $S$ be a short complex in the category `X.Modules` of sheaves of $\mathcal O_X$-modules, with objects $S.X_1 \xrightarrow{S.f} S.X_2 \xrightarrow{S.g} S.X_3$ and the composite $S.f$ followed by $S.g$ zero (this vanishing being part of the data of a short complex). Three hypotheses are imposed. First, $S.f$ is injective on sections over every open $U \subseteq X$: the map $S.f.app\,U$ on $\Gamma(S.X_1,U) \to \Gamma(S.X_2,U)$ is injective. Second, $S.g$ is locally surjective: for every open $U$, every section $s \in \Gamma(S.X_3,U)$ and every point $x \in U$ there are an open $V$, an inclusion $V \le U$ with $x \in V$, and a section over $V$ whose image under $S.g.app\,V$ is the restriction of $s$ to $V$. Third, the complex is locally exact in the middle: for every open $U$ and every $m \in \Gamma(S.X_2,U)$ with $S.g.app\,U\,m = 0$, and every $x \in U$, there are an open $V$ with $x \in V \le U$ such that the restriction of $m$ to $V$ lies in the image of $S.f.app\,V$. The conclusion is that $S$ is short exact in the sense of Mathlib's `ShortComplex.ShortExact`, i.e. $S.f$ is a monomorphism, $S.g$ is an epimorphism, and $S$ is exact.
--
--   This is the standard criterion for exactness of a sequence of $\mathcal O_X$-modules from sectionwise injectivity together with purely local surjectivity and local exactness, packaged for the abelian category of sheaves of modules on a scheme. It serves as a supplier of short exact sequences in that category, and is used in the construction of short exact sequences obtained by pushforward along a morphism of schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_shortExact_of_app_injective_of_locallySurjective_of_locallyExact.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

theorem AlgebraicGeometry.Scheme.Modules.shortExact_of_app_injective_of_locallySurjective_of_locallyExact
    {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hf : ∀ U : X.Opens, Function.Injective (S.f.app U))
    (hg : ∀ (U : X.Opens) (s : Γ(S.X₃, U)), ∀ x ∈ U, ∃ (V : X.Opens) (i : V ≤ U),
      x ∈ V ∧ S.X₃.presheaf.map (homOfLE i).op s ∈ Set.range (S.g.app V))
    (hfg : ∀ (U : X.Opens) (m : Γ(S.X₂, U)), S.g.app U m = 0 → ∀ x ∈ U, ∃ (V : X.Opens) (i : V ≤ U),
      x ∈ V ∧ S.X₂.presheaf.map (homOfLE i).op m ∈ Set.range (S.f.app V)) :
    S.ShortExact := by sorry
