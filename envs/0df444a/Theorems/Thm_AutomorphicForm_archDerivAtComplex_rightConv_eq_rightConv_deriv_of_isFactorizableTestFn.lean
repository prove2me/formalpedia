-- Prove2me | Theorems.Thm_AutomorphicForm_archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn
-- name    : AutomorphicForm.archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/8afe5d26-8513-5030-b612-5cd73fdb75b5
-- title:
--   Right convolution at a complex place: smoothing and integration by parts
-- statement:
--   Let $K$ be a number field, let $w$ be an infinite place of $K$ with `hw : w.IsComplex`, and let $d$ be one of the six directions `H`, `E`, `Fm`, `iH`, `iE`, `iFm`, so that `archFlowAtComplex hw d t` is the image in $\mathrm{GL}_2(\mathbb{A}_K)$ of the one-parameter subgroup of $\mathrm{GL}_2(\mathbb{C})$ at $w$ given by the split torus, the upper unipotent or the lower unipotent with parameter $t$ or $ti$, and `archDerivAtComplex hw d φ` is $g \mapsto \tfrac{d}{dt}\varphi(g\cdot\text{archFlowAtComplex }hw\,d\,t)|_{t=0}$. Three assertions are made simultaneously. (i) For all $\varphi,\alpha : \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ with $\varphi$ continuous and $\alpha$ a factorizable test function — that is, $\alpha(g)=f_\infty(\mathrm{glArch}\,g)\,f_f(\mathrm{glFin}\,g)$ with $f_\infty$ compactly supported and given by a $C^\infty$ function of the matrix entries viewed in the mixed space, and $f_f$ locally constant with compact support — the right convolution `rightConv K φ α`, the integral $g\mapsto\int \varphi(gx)\alpha(x)$ against the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, satisfies `IsArchSmoothAtComplex hw`, i.e. for every $g$ the map $e\mapsto(\text{rightConv}\,K\,\varphi\,\alpha)(g\cdot\text{archComplexLiftAt } hw\,e)$ is $C^\infty$ over $\mathbb{R}$ on the set of $e : \mathrm{Fin}\,2\to\mathrm{Fin}\,2\to\mathbb{C}$ of nonzero determinant, and its derivative along the flow equals the right convolution of $\varphi$ with the left derivative $y\mapsto\tfrac{d}{dt}\alpha(\text{archFlowAtComplex } hw\,d\,(-t)\cdot y)|_{t=0}$. (ii) For all $f_\infty$ on $\mathrm{GL}_2$ of the infinite adeles and all $f_f$ on $\mathrm{GL}_2$ of the finite adeles, if $f_\infty$ is an archimedean test factor in the above sense, then there is an archimedean test factor $f_\infty'$ with $y\mapsto\tfrac{d}{dt}\bigl(f_\infty(\mathrm{glArch}(\text{archFlowAtComplex } hw\,d\,(-t)\cdot y))\,f_f(\mathrm{glFin}(\text{archFlowAtComplex } hw\,d\,(-t)\cdot y))\bigr)|_{t=0}$ equal to $y\mapsto f_\infty'(\mathrm{glArch}\,y)\,f_f(\mathrm{glFin}\,y)$; no hypothesis is imposed on $f_f$. (iii) For all $\varphi,\gamma,\omega$ with $\varphi$ continuous, `IsArchSmoothAtComplex hw`-smooth and with continuous flow derivative, $\gamma$ continuous, compactly supported, smooth in the same sense and with continuous flow derivative, and $\omega$ continuous and invariant under right translation by the flow ($\omega(y\cdot\text{archFlowAtComplex } hw\,d\,t)=\omega(y)$ for all $y$ and $t$), one has $\text{rightConv}\,K\,\varphi\,\bigl((\text{archDerivAtComplex } hw\,d\,\gamma)\cdot\omega\bigr) = -\,\text{rightConv}\,K\,(\text{archDerivAtComplex } hw\,d\,\varphi)\,(\gamma\cdot\omega)$.
--
--   This is the complex-place instance of the Gårding smoothing calculus for right convolution on adelic $\mathrm{GL}(2)$: convolution by a factorizable test function produces vectors smooth at $w$, the flow derivative passes to the left derivative of the test function, and derivatives along a one-parameter subgroup may be integrated by parts against the right-invariant Haar measure. It is used for the smoothness and growth estimates of cut vectors at a complex place and for the action of the two Casimir operators at $w$ on smoothed vectors; the proof cites the continuity and compact support of factorizable test functions, the right-translation identity for `rightConv`, and the right invariance of the adelic $\mathrm{GL}_2$ Haar measure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm

theorem AutomorphicForm.archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn
    (K : Type) [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDirComplex) :
    (∀ φ α : AdelicGL2 (𝓞 K) K → ℂ, Continuous φ → IsFactorizableTestFn K α →
      IsArchSmoothAtComplex hw (rightConv K φ α) ∧
        archDerivAtComplex hw d (rightConv K φ α) =
          rightConv K φ (fun y => deriv (fun t : ℝ => α (archFlowAtComplex hw d (-t) * y)) 0)) ∧
    (∀ (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ),
      IsArchTestFactor K fa →
        ∃ fa' : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K fa' ∧
          (fun y : AdelicGL2 (𝓞 K) K =>
              deriv (fun t : ℝ => fa (glArch (𝓞 K) K (archFlowAtComplex hw d (-t) * y)) *
                ff (glFin (𝓞 K) K (archFlowAtComplex hw d (-t) * y))) 0) =
            fun y => fa' (glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y)) ∧
    (∀ φ γ ω : AdelicGL2 (𝓞 K) K → ℂ,
      Continuous φ → IsArchSmoothAtComplex hw φ → Continuous (archDerivAtComplex hw d φ) →
      Continuous γ → HasCompactSupport γ → IsArchSmoothAtComplex hw γ → Continuous (archDerivAtComplex hw d γ) →
      Continuous ω → (∀ (y : AdelicGL2 (𝓞 K) K) (t : ℝ), ω (y * archFlowAtComplex hw d t) = ω y) →
        rightConv K φ (fun y => archDerivAtComplex hw d γ y * ω y) =
          -rightConv K (archDerivAtComplex hw d φ) fun y => γ y * ω y) := by sorry
