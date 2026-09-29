-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isHaarMeasure_lintegral_comp_glArch_flowChart_mul_le
-- name    : AutomorphicForm.exists_isHaarMeasure_lintegral_comp_glArch_flowChart_mul_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/f58e9ab1-cae8-59ce-9fb2-83307fc93a7b
-- title:
--   Local Haar domination in archimedean flow-chart coordinates
-- statement:
--   Let $K$ be a number field, and let $L_0$ be a list whose entries are either a triple consisting of a real infinite place $w$ of $K$, a proof that it is real, and a direction in $\{H,E,F^-\}$, or a triple consisting of a complex place $w$, a proof that it is complex, and a direction in $\{H,E,F^-,iH,iE,iF^-\}$; assume $L_0$ has no repeated entry and contains every such triple. Fix a Borel measurable structure on $\mathrm{GL}_2$ of the infinite adele ring of $K$. To a real entry $(w,d)$ the statement associates the element $\mathrm{archFlowAt}$ of $\mathrm{GL}_2(\mathbb{A}_K)$ obtained by placing, at the component $w$ (via the identification of $w$'s completion with $\mathbb{R}$), the split-torus, upper unipotent or lower unipotent matrix with parameter $t$ according to $d$; to a complex entry it associates the analogous element with parameter $t$ or $ti$ placed at $w$ via the identification with $\mathbb{C}$. The chart sends $t \in \mathbb{R}^{|L_0|}$ to the ordered product $\prod_j \mathrm{flow}(L_0[j])(t_j)$, and $\mathrm{scal}$ sends $(a,b)$, indexed by the real and the complex places, to the product over real places of the central scalar unit $e^{a_w}$ placed at $w$ times the product over complex places of the central scalar unit $e^{b_w}$ placed at $w$. The assertion: there exist a regular Haar measure $\mu$ on $\mathrm{GL}_2$ of the infinite adele ring, a real $\ell$ with $0 < \ell \le 1/4$, a compact set $S$, and $c \in \mathbb{R}_{\ge 0}$ such that for every measurable $H$ with values in $[0,\infty]$, the integral of $H\bigl(\mathrm{glArch}(\mathrm{chart}(t)\cdot\mathrm{scal}(a,b))\bigr)$, taken with respect to the canonical volume measure over the box $[-\ell,\ell]^{|L_0|} \times [-\ell,\ell]^{r_1} \times \bar{D}(0,\ell)^{r_2}$, is at most $c \int_S H \, d\mu$; here $\mathrm{glArch}$ is the map on $\mathrm{GL}_2$ induced by the projection of the adele ring onto its infinite component.
--
--   This is the local comparison of Lebesgue measure in exponential coordinates of the second kind with Haar measure on $\mathrm{GL}_2(K_\infty)$: the nodup-and-complete hypothesis on $L_0$ guarantees that the chosen one-parameter directions together with the central directions span the Lie algebra, so that the chart composed with the central exponentials is a local diffeomorphism at the identity. It is cited by [`AutomorphicForm.exists_forall_lintegral_comp_flowChart_le_mul_lintegral_of_forall_mul_eq`](thm.html#AutomorphicForm.exists_forall_lintegral_comp_flowChart_le_mul_lintegral_of_forall_mul_eq), where integrals of automorphic test functions along flow charts are bounded by Haar integrals over compact sets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isHaarMeasure_lintegral_comp_glArch_flowChart_mul_le.lean

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

theorem AutomorphicForm.exists_isHaarMeasure_lintegral_comp_glArch_flowChart_mul_le
    (K : Type) [Field K] [NumberField K]
    (L₀ : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)))
    (hL₀ : L₀.Nodup) (hL₀' : ∀ d, d ∈ L₀)
    [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K))] [BorelSpace (GL (Fin 2) (InfiniteAdeleRing K))] :
    let flow : ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) → ℝ → AdelicGL2 (𝓞 K) K :=
      fun d t => Sum.elim (fun d => archFlowAt d.2.1 d.2.2 t) (fun d => archFlowAtComplex d.2.1 d.2.2 t) d
    let chart : (Fin L₀.length → ℝ) → AdelicGL2 (𝓞 K) K :=
      fun t => (List.ofFn fun j => flow (L₀.get j) (t j)).prod
    let scal : ({w : InfinitePlace K // w.IsReal} → ℝ) → ({w : InfinitePlace K // w.IsComplex} → ℂ) → AdelicGL2 (𝓞 K) K :=
      fun a b =>
        ((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).toList.map fun w =>
            archRealGLAt w.2 (Units.map (Matrix.scalar (Fin 2) : ℝ →+* Matrix (Fin 2) (Fin 2) ℝ).toMonoidHom
              (Units.mk0 (Real.exp (a w)) (Real.exp_ne_zero (a w))))).prod *
        ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).toList.map fun w =>
            archComplexGLAt w.2 (Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom
              (Units.mk0 (Complex.exp (b w)) (Complex.exp_ne_zero (b w))))).prod
    ∃ μ : Measure (GL (Fin 2) (InfiniteAdeleRing K)), μ.IsHaarMeasure ∧ μ.Regular ∧
      ∃ ℓ : ℝ, 0 < ℓ ∧ ℓ ≤ 1 / 4 ∧ ∃ S : Set (GL (Fin 2) (InfiniteAdeleRing K)), IsCompact S ∧ ∃ c : NNReal,
        ∀ H : GL (Fin 2) (InfiniteAdeleRing K) → ENNReal, Measurable H →
          ∫⁻ v in (Set.pi Set.univ fun _ : Fin L₀.length => Set.Icc (-ℓ) ℓ) ×ˢ
              ((Set.pi Set.univ fun _ : {w : InfinitePlace K // w.IsReal} => Set.Icc (-ℓ) ℓ) ×ˢ
                (Set.pi Set.univ fun _ : {w : InfinitePlace K // w.IsComplex} => Metric.closedBall (0 : ℂ) ℓ)),
            H (glArch (𝓞 K) K (chart v.1 * scal v.2.1 v.2.2)) ≤
          (c : ENNReal) * ∫⁻ g in S, H g ∂μ := by sorry
