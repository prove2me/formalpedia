-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_of_hasCompactSupport
-- name    : AutomorphicForm.exists_isSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_of_hasCompactSupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/8b41bf6e-aaf9-5033-bbe5-eb9a9a5acb3b
-- title:
--   Continuous section functions at regular semisimple γ over K_∞
-- statement:
--   Let $K$ be a number field, and let $G = \mathrm{GL}_2(\mathbb{A}_{K,\infty})$ be the group of invertible $2\times 2$ matrices over the infinite adele ring of $K$. Let $\gamma \in G$ satisfy [`AutomorphicForm.IsRegularSemisimple`](def/AutomorphicForm_LocalOrbitalBase.html#L402), i.e. $(\mathrm{tr}\,\gamma)^2 - 4\det\gamma$ is a unit of $\mathbb{A}_{K,\infty}$. Let $T =$ the centralizer subgroup of $\{\gamma\}$ in $G$, equipped with the Borel $\sigma$-algebra of its subspace topology ([`AutomorphicForm.centralizerBorel`](def/AutomorphicForm_TwistedOrbital.html#L62)), and let $\tau$ be a Haar measure on $T$ for that $\sigma$-algebra. Let $f \colon G \to \mathbb{C}$ be any function with compact support; no continuity or measurability of $f$ is assumed. The conclusion asserts the existence of $w \colon G \to \mathbb{R}$ such that [`AutomorphicForm.IsSectionFnOn`](def/AutomorphicForm_TwistedOrbital.html#L239) holds for $\mathbb{A}_{K,\infty}$, $\gamma$, $\tau$, $f$, $w$ and $w$ is continuous; unfolded, $w$ takes only nonnegative values, is measurable for the Borel $\sigma$-algebra of $G$, has compact support, is continuous, and satisfies $\int_{T} w(tx)\,d\tau(t) = 1$ for every $x \in G$ with $f(x^{-1}\gamma x) \neq 0$.
--
--   This is the archimedean existence statement underlying orbital integrals on $\mathrm{GL}_2$: a continuous nonnegative compactly supported weight normalising the $T$-cosets along the orbit of $\gamma$ that meets the support of $f$, so that the integral of $f(x^{-1}\gamma x)w(x)$ over $G$ computes an orbital integral. It is obtained by specialising the corresponding twisted statement ([`AutomorphicForm.exists_isTwistedSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_normString_of_hasCompactSupport`](thm.html#AutomorphicForm.exists_isTwistedSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_normString_of_hasCompactSupport)), and is used in the archimedean comparisons of orbital and twisted orbital integrals in the trace formula part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_of_hasCompactSupport.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField MeasureTheory

theorem AutomorphicForm.exists_isSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_of_hasCompactSupport
    (K : Type) [Field K] [NumberField K]
    (γ : GL (Fin 2) (InfiniteAdeleRing K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) γ))
    [@Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) γ) τ]
    (f : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hf : HasCompactSupport f) :
    ∃ w : GL (Fin 2) (InfiniteAdeleRing K) → ℝ,
      AutomorphicForm.IsSectionFnOn (InfiniteAdeleRing K) γ τ f w ∧ Continuous w := by sorry
