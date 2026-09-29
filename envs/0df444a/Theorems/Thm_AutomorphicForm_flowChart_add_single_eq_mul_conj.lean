-- Prove2me | Theorems.Thm_AutomorphicForm_flowChart_add_single_eq_mul_conj
-- name    : AutomorphicForm.flowChart_add_single_eq_mul_conj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/08f85a2b-69be-59b5-b1dc-3c612a56f969
-- title:
--   Moving one chart coordinate: right translation by a conjugated flow
-- statement:
--   Let $K$ be a number field and let $L_0$ be a list whose entries are data of two kinds: either a real infinite place $w$ of $K$ (together with a proof that $w$ is real) and a direction $d \in \{H,E,F^-\}$, or a complex infinite place $w$ (with a proof that it is complex) and a direction $d \in \{H,E,F^-,iH,iE,iF^-\}$. Fix an index $j$ into $L_0$, a vector $t \in \mathbb{R}^{\operatorname{length} L_0}$ and $s \in \mathbb{R}$. For a real datum the flow at parameter $u$ is the image in $\mathrm{GL}_2$ of the adeles of $K$ of the matrix $\mathrm{archFlowMatrix}\,d\,u \in \mathrm{GL}_2(\mathbb{R})$ — namely $\mathrm{diag}(e^u,e^{-u})$ for $H$, $\begin{pmatrix}1&u\\0&1\end{pmatrix}$ for $E$, $\begin{pmatrix}1&0\\u&1\end{pmatrix}$ for $F^-$ — transported by the isomorphism $\mathbb{R} \cong K_w$ and included at the place $w$; for a complex datum one uses the corresponding matrices over $\mathbb{C}$ with entry parameter $u$ or $ui$, transported by $\mathbb{C} \cong K_w$. The chart $\mathrm{chart}(t)$ is the product, in list order, of the flows of the successive entries of $L_0$ at the parameters $t_i$. For an infinite place $w$, $\mathrm{tailMatR}(w)$ (resp. $\mathrm{tailMatC}(w)$) is the ordered product over the indices $i > j$ of $\mathrm{archFlowMatrix}$ (resp. $\mathrm{archFlowMatrixComplex}$) of the $i$-th direction at $t_i$ when the $i$-th entry is a real (resp. complex) datum at the place $w$, and the identity matrix for all other indices. The assertion is: if the $j$-th entry is a real datum at the place $w$ with direction $d$, then $\mathrm{chart}(t + s\,e_j)$ equals $\mathrm{chart}(t)$ times the element of adelic $\mathrm{GL}_2$ obtained by placing $M^{-1}\,(\mathrm{archFlowMatrix}\,d\,s)\,M$ at $w$, where $M = \mathrm{tailMatR}(w)$; and symmetrically, for a complex datum at $w$ with direction $d$, with $\mathrm{archFlowMatrixComplex}\,d\,s$ conjugated by $M = \mathrm{tailMatC}(w)$ and placed at $w$.
--
--   This is the cocycle computation underlying differentiation of adelic automorphic forms along a chart built from one-parameter subgroups at the infinite places: varying the $j$-th coordinate amounts to right translation by the $j$-th one-parameter subgroup conjugated by the later factors at the same place, the factors at other places commuting with it. It is used in the estimate bounding iterated derivatives of a form composed with such a chart by sums of archimedean invariant derivatives.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_flowChart_add_single_eq_mul_conj.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.InfinitePlace
open AutomorphicForm
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel
open scoped Classical

theorem AutomorphicForm.flowChart_add_single_eq_mul_conj
    (K : Type) [Field K] [NumberField K]
    (L₀ : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)))
    (j : Fin L₀.length) (t : Fin L₀.length → ℝ) (s : ℝ) :
    let flow : ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) → ℝ → AdelicGL2 (𝓞 K) K :=
      fun d t => Sum.elim (fun d => archFlowAt d.2.1 d.2.2 t) (fun d => archFlowAtComplex d.2.1 d.2.2 t) d
    let chart : (Fin L₀.length → ℝ) → AdelicGL2 (𝓞 K) K :=
      fun t => (List.ofFn fun i => flow (L₀.get i) (t i)).prod
    let tailMatR : InfinitePlace K → GL (Fin 2) ℝ := fun w =>
      ((List.ofFn fun i : Fin L₀.length => match L₀.get i with
        | Sum.inl d => if d.1 = w then archFlowMatrix d.2.2 (t i) else 1
        | Sum.inr _ => (1 : GL (Fin 2) ℝ)).drop (j.val + 1)).prod
    let tailMatC : InfinitePlace K → GL (Fin 2) ℂ := fun w =>
      ((List.ofFn fun i : Fin L₀.length => match L₀.get i with
        | Sum.inr d => if d.1 = w then archFlowMatrixComplex d.2.2 (t i) else 1
        | Sum.inl _ => (1 : GL (Fin 2) ℂ)).drop (j.val + 1)).prod
    match L₀.get j with
    | Sum.inl d => chart (t + s • (Pi.single j (1 : ℝ) : Fin L₀.length → ℝ)) =
        chart t * archRealGLAt d.2.1 ((tailMatR d.1)⁻¹ * archFlowMatrix d.2.2 s * tailMatR d.1)
    | Sum.inr d => chart (t + s • (Pi.single j (1 : ℝ) : Fin L₀.length → ℝ)) =
        chart t * archComplexGLAt d.2.1 ((tailMatC d.1)⁻¹ * archFlowMatrixComplex d.2.2 s * tailMatC d.1) := by sorry
