-- Prove2me | Theorems.Thm_AutomorphicForm_archHeight_glArch_centralScalar_mul
-- name    : AutomorphicForm.archHeight_glArch_centralScalar_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/2d85b103-28cd-5b41-b3a8-fef01c3fcc6f
-- title:
--   Invariance of the archimedean height under central scalars
-- statement:
--   Let $F$ be a number field, let $z$ be a unit of the adele ring $\mathbb{A}_F$ of $F$ (formed with respect to the ring of integers $\mathcal{O}_F$), and let $g$ be an element of $\mathrm{GL}_2(\mathbb{A}_F)$. Write $\mathrm{centralScalar}$ for the homomorphism sending an idele $z$ to the scalar matrix $\mathrm{diag}(z,z)$ in $\mathrm{GL}_2(\mathbb{A}_F)$, and $\mathrm{glArch}$ for the homomorphism $\mathrm{GL}_2(\mathbb{A}_F) \to \mathrm{GL}_2(\mathbb{A}_{F,\infty})$ obtained by applying, entrywise, the ring homomorphism $\mathrm{adeleArch}$ that takes an adele to its infinite component. For $h \in \mathrm{GL}_2(\mathbb{A}_{F,\infty})$, $\mathrm{archHeight}\,F\,h$ is the product over the infinite places $v$ of $F$ of $\bigl(\lVert \det h_v \rVert / \mathrm{rowNormSq}(h_v)\bigr)^{v.\mathrm{mult}}$, where $h_v$ denotes the image of $h$ in $\mathrm{GL}_2(F_v)$ under the place-$v$ evaluation and $\mathrm{rowNormSq}$ is the row-norm quantity of the underlying matrix. The assertion is the equality $$\mathrm{archHeight}\,F\,\bigl(\mathrm{glArch}(\mathrm{centralScalar}(z)\cdot g)\bigr) = \mathrm{archHeight}\,F\,\bigl(\mathrm{glArch}(g)\bigr).$$ Thus the archimedean height, pulled back along $\mathrm{glArch}$, is unchanged by left multiplication by a central idelic scalar, so it factors through the central quotient $Z(\mathbb{A}_F)\backslash \mathrm{GL}_2(\mathbb{A}_F)$.
--
--   This is the central-character invariance of the classical $\mathrm{GL}_2$ height $y = \lvert\det\rvert / \lVert\text{row}\rVert^2$ used to define windowed Siegel sets, and it is what allows height estimates to be made on the central quotient. It is used in the rapid-decay estimate for the Bruhat–Eisenstein series minus its constant term and in the construction of a level at which a continuous cuspidal Hecke eigenform is arithmetically realisable.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archHeight_glArch_centralScalar_mul.lean

import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AutomorphicForm.archHeight_glArch_centralScalar_mul (F : Type) [Field F] [NumberField F]
    (z : (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)ˣ)
    (g : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers F) F) :
    AutomorphicForm.WindowedSiegel.archHeight F
        (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers F) F
          (AutomorphicForm.centralScalar (NumberField.RingOfIntegers F) F z * g))
      = AutomorphicForm.WindowedSiegel.archHeight F
          (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers F) F g) := by sorry
