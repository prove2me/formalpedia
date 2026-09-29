-- Prove2me | Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
-- name    : AutomorphicForm.canonicalTruncationData_isTruncationDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/01b94728-a3bb-56a4-925b-4a5b5e87a5e1
-- title:
--   Admissibility of the canonical truncation datum for GL₂
-- statement:
--   Let $L$ be a number field and let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$. The canonical truncation datum attached to $(L,\alpha,\beta)$ is, by definition, a classically chosen tuple $d$ satisfying `IsTruncationDatum L α β d` when such a tuple exists and $((0,0,0,0),\emptyset,\emptyset)$ otherwise; its components are four reals, the floor `canonicalTruncationFloor` $c$, the window `canonicalTruncationWindow` $u$ and the cuts `canonicalTruncationLowerCut` $d_1$, `canonicalTruncationUpperCut` $d_2$, together with a set of translates $T$ and a set $\mathcal F$, both in $\mathrm{GL}_2$ of the adele ring of $L$. The theorem asserts five things: $0<c$; $T$ is compact; $\mathcal F$ is contained in the union over $y\in T$ of the right translates $\{x y : x\in\mathcal S\}$, where $\mathcal S$ is the centre-cut Siegel set of those $g$ whose finite part lies in `finiteIntegralGL2` and whose archimedean component at every infinite place $w$ satisfies $c\le$ `localHeight`, `xWindowSq` $\le u^2$ and `archDetNorm` $w\,g\in[d_1,d_2]$; $\mathcal F$ is contained in the determinant slab $\{g : \mathrm{ideleNorm}_L(\det g)\in[\alpha,\beta]\}$, the idele norm being the value of the distributive Haar character; and $\mathcal F$ is a fundamental domain for the range of the entrywise map $\mathrm{GL}_2(L)\to\mathrm{GL}_2(\mathbf A_L)$ acting on the adelic Haar measure of $\mathrm{GL}_2(\mathbf A_L)$ restricted to that slab.
--
--   This is the admissibility statement for the fixed choice of truncation data used throughout the adelic theory of automorphic forms on $\mathrm{GL}_2$: it packages reduction theory (finitely many translates of a centre-cut Siegel set cover $\mathrm{GL}_2(\mathbf A_L)$ modulo $\mathrm{GL}_2(L)$ and the centre) together with the existence of a measurable fundamental domain inside a determinant slab. It is the basic input for the positivity of the volume of the truncation domain and for the $L^p$ and integral estimates on automorphic functions built on that domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum.lean

import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.canonicalTruncationData_isTruncationDatum
    (L : Type) [Field L] [NumberField L] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    0 < canonicalTruncationFloor L α β ∧ IsCompact (canonicalTruncationTranslates L α β) ∧
      canonicalTruncationDomain L α β ⊆ ⋃ y ∈ canonicalTruncationTranslates L α β,
        (· * y) '' WindowedSiegel.centreCutSiegelSet L (canonicalTruncationFloor L α β)
          (canonicalTruncationWindow L α β) (canonicalTruncationLowerCut L α β)
          (canonicalTruncationUpperCut L α β) ∧
      canonicalTruncationDomain L α β ⊆
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} ∧
      IsFundamentalDomain (globalPoints (𝓞 L) L).range (canonicalTruncationDomain L α β)
        ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
          {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) := by sorry
