-- Prove2me | Theorems.Thm_AutomorphicForm_su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional
-- name    : AutomorphicForm.su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/5d28b006-1db1-5f86-b034-b64fd0b4d7d3
-- title:
--   Finite-dimensional mathfraksu(2)-calculus and circle-weight decomposition at a complex place
-- statement:
--   Let $F$ be a number field, $w$ an infinite place of $F$ with $w$ complex, and let $Y$ be a finite-dimensional $\mathbb{C}$-subspace of the space of functions $\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ (here $\mathrm{GL}_2$ over the adele ring of $\mathcal{O}_F$, $F$), subject to two hypotheses: every $y\in Y$ satisfies `IsArchSmoothAtComplex hw`, that is, for each $g$ the map $e\mapsto y(g\cdot\mathtt{archComplexLiftAt}\,hw\,e)$ sending a $2\times 2$ complex matrix $e$ with $\det e\neq 0$ to the value of $y$ at $g$ times the element of $\mathrm{GL}_2(\mathbb{A}_F)$ obtained by placing $e$ at $w$ is $C^\infty$ (real sense) on $\{\det\neq 0\}$; and $Y$ is stable under right translation by $\mathtt{rowIsometryInclAt}_0\,F\,w\,k$ for every $k$ in the group $\mathtt{rowIsometrySubgroup}_0\,(F_w)$. Write $D_0 y=\mathtt{archDerivAtComplex}\,hw\,iH\,y$, $D_1y=\mathtt{archDerivAtComplex}\,hw\,Fm\,y-\mathtt{archDerivAtComplex}\,hw\,E\,y$ and $D_2y=\mathtt{archDerivAtComplex}\,hw\,iE\,y+\mathtt{archDerivAtComplex}\,hw\,iFm\,y$, each $\mathtt{archDerivAtComplex}\,hw\,d\,y$ being $g\mapsto \frac{d}{dt}y(g\cdot\mathtt{archFlowAtComplex}\,hw\,d\,t)|_{t=0}$; and let $M(s)=\mathtt{archFlowAtComplex}\,hw\,iH\,s$, while $R(s)$ and $S(s)$ are the elements obtained by placing at $w$ the matrices $\begin{pmatrix}\cos s&-\sin s\\ \sin s&\cos s\end{pmatrix}$ and $\begin{pmatrix}\cos s& i\sin s\\ i\sin s&\cos s\end{pmatrix}$. The conclusion is fourfold: (i) $Y$ is stable under $D_0$, $D_1$, $D_2$; (ii) for $y\in Y$, every $g$ and every real $s$, the functions $t\mapsto y(gM(t))$, $t\mapsto y(gR(t))$, $t\mapsto y(gS(t))$ are differentiable at $s$ with derivatives $(D_0y)(gM(s))$, $(D_1y)(gR(s))$, $(D_2y)(gS(s))$; (iii) every $\mathbb{C}$-subspace $S\subseteq Y$ stable under $D_0,D_1,D_2$ is stable under right translation by $M(s)$, $R(s)$, $S(s)$ for all real $s$; (iv) every $y\in Y$ is a finite sum $y=\sum_{m\in \mathtt{ms}} y_m$ over a finite set of integers, with each $y_m\in Y$ of circle weight $m$ at $w$ (that is, $y_m(g\cdot\mathtt{archCircleAt}\,hw\,\zeta)=\zeta^m y_m(g)$ for all units $\zeta$ with $\lVert\zeta\rVert=1$ and all $g$) and $D_0y_m=im\,y_m$.
--
--   This packages the finite-dimensional calculus of the compact group at a complex place: a finite-dimensional right-$K_w$-stable space of functions smooth at $w$ is stable under the three $\mathfrak{su}(2)$-directions, the flow derivatives are genuine derivatives at every parameter value, Lie-algebra stability of a subspace is equivalent in effect to stability under the three one-parameter subgroups, and the space splits into circle weight spaces with $D_0$ acting by $im$. It is the analytic input for the construction of $\mathfrak{su}(2)$-strings and highest-weight vectors in cuspidal constituents at complex places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) [FiniteDimensional ℂ Y]
    (hYs : ∀ y ∈ Y, IsArchSmoothAtComplex hw y)
    (hYK : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ y ∈ Y,
      (fun g => y (g * rowIsometryInclAt₀ F w k)) ∈ Y) :
    let D₀ : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ) := fun y => archDerivAtComplex hw .iH y
    let D₁ : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ) :=
      fun y => archDerivAtComplex hw .Fm y - archDerivAtComplex hw .E y
    let D₂ : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ) :=
      fun y => archDerivAtComplex hw .iE y + archDerivAtComplex hw .iFm y
    let Mrot : ℝ → AdelicGL2 (𝓞 F) F := fun s => archFlowAtComplex hw .iH s
    let Rrot : ℝ → AdelicGL2 (𝓞 F) F := fun s => archComplexLiftAt hw
      !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)]
    let Srot : ℝ → AdelicGL2 (𝓞 F) F := fun s => archComplexLiftAt hw
      !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)]
    (∀ y ∈ Y, D₀ y ∈ Y ∧ D₁ y ∈ Y ∧ D₂ y ∈ Y) ∧
    (∀ y ∈ Y, ∀ (g : AdelicGL2 (𝓞 F) F) (s : ℝ),
      HasDerivAt (fun t : ℝ => y (g * Mrot t)) (D₀ y (g * Mrot s)) s ∧
      HasDerivAt (fun t : ℝ => y (g * Rrot t)) (D₁ y (g * Rrot s)) s ∧
      HasDerivAt (fun t : ℝ => y (g * Srot t)) (D₂ y (g * Srot s)) s) ∧
    (∀ S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), S ≤ Y →
      (∀ y ∈ S, D₀ y ∈ S ∧ D₁ y ∈ S ∧ D₂ y ∈ S) →
      ∀ y ∈ S, ∀ s : ℝ, (fun g => y (g * Mrot s)) ∈ S ∧ (fun g => y (g * Rrot s)) ∈ S ∧
        (fun g => y (g * Srot s)) ∈ S) ∧
    (∀ y ∈ Y, ∃ (ms : Finset ℤ) (ys : ℤ → (AdelicGL2 (𝓞 F) F → ℂ)),
      (∀ m ∈ ms, ys m ∈ Y ∧ HasCircleWeightAt hw m (ys m) ∧ D₀ (ys m) = (Complex.I * (m : ℂ)) • ys m) ∧
      y = ∑ m ∈ ms, ys m) := by sorry
