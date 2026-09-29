-- Prove2me | Theorems.Thm_AutomorphicForm_IsFactorizableTestFn_isArchSmoothAtComplex_and_archDerivAtComplex_eq_tensor
-- name    : AutomorphicForm.IsFactorizableTestFn.isArchSmoothAtComplex_and_archDerivAtComplex_eq_tensor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/a89b2081-ed4a-5e4c-8b10-504de95536fb
-- title:
--   Factorizable test functions: smoothness and tensor flow derivatives at a complex place
-- statement:
--   Let $K$ be a number field, $w$ an infinite place of $K$ with `w.IsComplex` witnessed by `hw`, and $\alpha : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ a function satisfying `IsFactorizableTestFn K α`, i.e. $\alpha(g) = f_\infty(g_\infty)\,f_{\mathrm f}(g_{\mathrm f})$ for some $f_\infty$ on $\mathrm{GL}_2$ of the infinite adeles that is of the form $\Phi \circ \text{archEntries}$ with $\Phi$ a $C^\infty$ (over $\mathbb{R}$) function of the matrix entries read in the mixed space $\mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$ and has compact support, and some locally constant compactly supported $f_{\mathrm f}$ on $\mathrm{GL}_2$ of the finite adeles. The assertion is twofold. First, $\alpha$ is smooth at $w$ in the sense of `IsArchSmoothAtComplex`: for every $g$, the map $e \mapsto \alpha(g \cdot \text{archComplexLiftAt } hw\, e)$ on $2\times 2$ arrays of complex numbers is $C^\infty$ over $\mathbb{R}$ on the locus where $\det e \ne 0$. Second, there exist an archimedean test factor $fa$ and a finite test factor $ff$ with $\alpha(y) = fa(y_\infty)\,ff(y_{\mathrm f})$ for all $y$, such that for each of the six real directions $d \in \{H, E, F, iH, iE, iF\}$ at $w$ there is an archimedean test factor $fa'$ with $(\text{archDerivAtComplex } hw\, d\, \alpha)(y) = fa'(y_\infty)\,ff(y_{\mathrm f})$ for all $y$, where the derivative is $\frac{d}{dt}\big|_{t=0}\alpha(y \cdot \exp(td)_w)$. The finite factor $ff$ is the same for $\alpha$ and for all six derivatives.
--
--   This is the complex-place counterpart of the corresponding statement at a real place: the class of factorizable test functions on $\mathrm{GL}_2(\mathbb{A}_K)$ is stable under the six right-flow derivatives in the directions of $\mathfrak{sl}_2(\mathbb{C})$ viewed as a real Lie algebra, with the finite factor untouched. It is used in the treatment of the two complex-place Casimir operators on adelic automorphic forms, in particular to show that iterated flow derivatives of such test functions are again factorizable test functions and so continuous with compact support, as required for the convolution arguments that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_IsFactorizableTestFn_isArchSmoothAtComplex_and_archDerivAtComplex_eq_tensor.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.IsFactorizableTestFn.isArchSmoothAtComplex_and_archDerivAtComplex_eq_tensor
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hα : IsFactorizableTestFn K α) :
    IsArchSmoothAtComplex hw α ∧
    ∃ (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ),
      IsArchTestFactor K fa ∧ IsFinTestFactor K ff ∧
      (∀ y, α y = fa (glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y)) ∧
      ∀ d : ArchDirComplex, ∃ fa' : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K fa' ∧
        ∀ y, archDerivAtComplex hw d α y = fa' (glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y) := by sorry
