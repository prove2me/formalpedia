-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_and_supportedIn
-- name    : AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_prodKerGraph_and_supportedIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/2013fe9e-2387-50f9-97c7-5ed17ddc00f4
-- title:
--   Sums of points in the smooth locus give relative divisors
-- statement:
--   Let $f\colon\mathcal C\to S$ be a separated morphism of schemes, and let $U\subseteq\mathcal C$ be an open subscheme such that the composite of the inclusion $U\hookrightarrow\mathcal C$ with $f$ is smooth of relative dimension $1$; no smoothness is assumed of $f$ itself away from $U$. Let $e$ be a natural number, let $g\colon T\to S$ be a morphism, and let $a_0,\dots,a_{e-1}\colon T\to\mathcal C$ be morphisms with $a_i$ followed by $f$ equal to $g$ for each $i$, and with the range of the underlying continuous map of each $a_i$ contained in the open set $U$. The assertion is the existence of a term $D$ of the structure $\mathrm{RelEffCartierDiv}\ f\ e\ g$ — that is, of a quasi-coherent ideal sheaf datum $I$ on $\mathcal C\times_S T$ such that the closed immersion of the associated closed subscheme followed by the projection $\mathrm{pullback.snd}$ to $T$ is finite, flat and locally of finite presentation, with fibre rank exactly $e$ at every point $t$ of $T$ — whose ideal $D.I$ equals $\mathrm{prodKerGraph}\ f\ a\ ha$, namely the product over $i\in\mathrm{Fin}\ e$ of the kernel ideals of the graph morphisms $\mathrm{graphOver}\ f\ (a_i) = \langle a_i,\mathrm{id}_T\rangle\colon T\to\mathcal C\times_S T$, and which is supported in $U$, i.e. the support of $D.I$ is contained in the preimage of $U$ under the projection $\mathrm{pullback.fst}$ to $\mathcal C$.
--
--   This realises the divisor $\sum_i (a_i)$ attached to an $e$-tuple of $S$-valued points lying in the relative smooth locus as a genuine relative effective Cartier divisor of degree $e$ on $\mathcal C\times_S T\to T$, in the form needed for families of curves that are only smooth along $U$ (semistable models). It feeds the relative Picard and Euler-characteristic computations for two-line degenerations and for the vanishing of $H^1$ of chart and fibre modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_and_supportedIn.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_prodKerGraph_and_supportedIn
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] (U : 𝒞.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ f)]
    {e : ℕ} {T : Scheme.{u}} {g : T ⟶ S} (a : Fin e → (T ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g)
    (haU : ∀ i, Set.range (a i).base ⊆ (U : Set 𝒞)) :
    ∃ D : RelEffCartierDiv f e g, D.I = prodKerGraph f a ha ∧ D.SupportedIn U := by sorry
