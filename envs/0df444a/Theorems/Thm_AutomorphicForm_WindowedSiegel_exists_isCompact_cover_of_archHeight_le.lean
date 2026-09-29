-- Prove2me | Theorems.Thm_AutomorphicForm_WindowedSiegel_exists_isCompact_cover_of_archHeight_le
-- name    : AutomorphicForm.WindowedSiegel.exists_isCompact_cover_of_archHeight_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/0cce0f61-b356-5d3f-b2d3-e3bef1a62930
-- title:
--   Compact cover of the low part of a windowed Siegel set
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal{O}_F$ and adele ring $\mathbb{A}_F$, and let $c$, $u$, $T'$ be real numbers with $c>0$. The assertion is the existence of a set $K$ of adelic matrices in $\mathrm{GL}_2(\mathbb{A}_F)$ (written [`AutomorphicForm.AdelicGL2`](def/AutomorphicForm_AdelicLsXi.html#L12)) that is compact and has the following property. Let $x\in\mathrm{GL}_2(\mathbb{A}_F)$ lie in the integrally windowed Siegel set `integralWindowedSiegelSet F c u`, i.e. the finite component `glFin` of $x$ lies in the subgroup `finiteIntegralGL2` of $\mathrm{GL}_2$ of the finite adeles, the archimedean height $\mathrm{archHeight}$ of the archimedean component `glArch` of $x$ — the product over the infinite places $v$ of $F$ of $\bigl(\|\det\|/\mathrm{rowNormSq}\bigr)^{v.\mathrm{mult}}$ of the component of $x$ at $v$ — is at least $c$, and at every infinite place $v$ the window coordinate $\mathrm{xWindowSq}$, namely $\mathrm{topNormSq}/\mathrm{rowNormSq}$ minus the square of the local height, is at most $u^2$; and suppose in addition that this archimedean height of $x$ is at most $T'$. Then there are $\gamma\in\mathrm{GL}_2(F)$ with lower left entry $\gamma_{10}=0$ and an idele $z\in\mathbb{A}_F^{\times}$ such that the product of the entrywise image `globalPoints` of $\gamma$, of $x$, and of the central scalar matrix `centralScalar` attached to $z$ lies in $K$.
--
--   This is the reduction-theoretic statement that the height-bounded (low) part of an integrally windowed Siegel set in $\mathrm{GL}_2(\mathbb{A}_F)$ is contained in $B(F)\cdot K\cdot Z(\mathbb{A}_F)$ for a single compact $K$, the Borel subgroup being realised through the condition $\gamma_{10}=0$. It is used in the estimates showing that Bruhat–Eisenstein series minus their constant terms are rapidly decreasing, and in the comparisons of finite sums with constant terms on translates of centre-cut Siegel sets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_WindowedSiegel_exists_isCompact_cover_of_archHeight_le.lean

import Definitions.Def_AutomorphicForm_WindowedSiegelSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AutomorphicForm.WindowedSiegel.exists_isCompact_cover_of_archHeight_le
    (F : Type) [Field F] [NumberField F] (c u T' : ℝ) (hc : 0 < c) :
    ∃ K : Set (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers F) F),
      IsCompact K ∧
        ∀ x ∈ AutomorphicForm.WindowedSiegel.integralWindowedSiegelSet F c u,
          AutomorphicForm.WindowedSiegel.archHeight F
              (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers F) F x) ≤ T' →
            ∃ γ : Matrix.GeneralLinearGroup (Fin 2) F,
              ∃ z : (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)ˣ,
                (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
                  AutomorphicForm.globalPoints (NumberField.RingOfIntegers F) F γ * x *
                      AutomorphicForm.centralScalar (NumberField.RingOfIntegers F) F z ∈ K := by sorry
