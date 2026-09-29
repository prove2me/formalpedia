-- Prove2me | Theorems.Thm_AutomorphicForm_exists_eq_mul_archSupportedAt_of_mem_maximalCompactAt_empty
-- name    : AutomorphicForm.exists_eq_mul_archSupportedAt_of_mem_maximalCompactAt_empty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/525b2317-cee4-59c6-9cc7-b95ea062a043
-- title:
--   Peeling one archimedean place off a maximal compact element
-- statement:
--   Let $F$ be a number field and let $k$ be an element of $\mathrm{GL}_2(\mathbb{A}_F)$ (written `AdelicGL2 (𝓞 F) F`) lying in `maximalCompactAt F ∅`, that is: the finite part $\mathrm{glFin}\,k$ lies in `finiteIntegralGL2 (𝓞 F) F`, its component at every finite place $v$ of $\mathcal{O}_F$ is trivial (the subgroup is intersected with the kernels of `finComponent` composed with `glFin` over the complement of the empty set of height-one primes), and for every infinite place $w'$ the component $\mathrm{archComponent}_{w'}(\mathrm{glArch}\,k)$ satisfies `IsRowIsometry`, i.e. its determinant has norm $1$ and $(x,y)\mapsto (xk_{00}+yk_{10},\,xk_{01}+yk_{11})$ preserves $\lVert x\rVert^2+\lVert y\rVert^2$. Let $w$ be an infinite place of $F$. Then there exist $k_1,k_2\in\mathrm{GL}_2(\mathbb{A}_F)$ with $k=k_1k_2$ and $k_1k_2=k_2k_1$, such that $\mathrm{glFin}\,k_1=1$, the archimedean component of $k_1$ at every infinite place $w'\neq w$ is $1$, its component at $w$ equals that of $k$, every archimedean component of $k_1$ is a row isometry, while $k_2$ again lies in `maximalCompactAt F ∅` and has trivial archimedean component at $w$.
--
--   This is the peeling step for an induction over the infinite places: an element of the maximal compact subgroup with trivial components at all finite places is factored into a part supported at a single archimedean place $w$ and a commuting remainder that is trivial at $w$. It is used in the analysis of archimedean right translations of Weyl intertwining integrals for flat families.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_eq_mul_archSupportedAt_of_mem_maximalCompactAt_empty.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Meromorphic.Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology
open scoped NNReal

theorem AutomorphicForm.exists_eq_mul_archSupportedAt_of_mem_maximalCompactAt_empty
    (F : Type) [Field F] [NumberField F] (k : AdelicGL2 (𝓞 F) F) (_hk : k ∈ maximalCompactAt F ∅) (w : InfinitePlace F) :
    ∃ k₁ k₂ : AdelicGL2 (𝓞 F) F,
      k = k₁ * k₂ ∧ k₁ * k₂ = k₂ * k₁ ∧
      glFin (𝓞 F) F k₁ = 1 ∧
      (∀ w' : InfinitePlace F, w' ≠ w → archComponent F w' (glArch (𝓞 F) F k₁) = 1) ∧
      archComponent F w (glArch (𝓞 F) F k₁) = archComponent F w (glArch (𝓞 F) F k) ∧
      (∀ w' : InfinitePlace F, IsRowIsometry (archComponent F w' (glArch (𝓞 F) F k₁))) ∧
      k₂ ∈ maximalCompactAt F ∅ ∧ archComponent F w (glArch (𝓞 F) F k₂) = 1 := by sorry
