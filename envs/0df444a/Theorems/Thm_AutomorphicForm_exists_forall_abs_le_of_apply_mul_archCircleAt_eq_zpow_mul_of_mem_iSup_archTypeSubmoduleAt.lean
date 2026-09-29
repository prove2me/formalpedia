-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_abs_le_of_apply_mul_archCircleAt_eq_zpow_mul_of_mem_iSup_archTypeSubmoduleAt
-- name    : AutomorphicForm.exists_forall_abs_le_of_apply_mul_archCircleAt_eq_zpow_mul_of_mem_iSup_archTypeSubmoduleAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/9e7799e9-f87d-5cd1-a7a8-fabe6caec4e2
-- title:
--   Uniform weight window at complex places for type sums
-- statement:
--   Let $K$ be a number field and let $\mathtt{tys}$ be an archimedean type family for $K$: for each infinite place $w$ a natural number $\mathtt{card}\,w$ together with, for each $i < \mathtt{card}\,w$, a type $\mathtt{rep}\,w\,i$ consisting of an integer $n$ and a representation of the group $\mathtt{rowIsometrySubgroup₀}\,w.\mathrm{Completion}$ on $\mathbb{C}^n$ (no continuity is required of these representations). The assertion is that there exists $n_0 \in \mathbb{N}$, depending only on $K$ and on the family, with the following property. Let $w$ be a complex infinite place of $K$, and let $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous and lie in the join (sum) over $i < \mathtt{card}\,w$ of the submodules $\mathtt{archTypeSubmoduleAt}\,K\,w\,(\mathtt{rep}\,w\,i)$, where the submodule attached to a type $\tau$ is the $\mathbb{C}$-span of all functions lying in the range of some linear map $T : \mathbb{C}^{n} \to (\mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C})$ that is right equivariant for the inclusion $\mathtt{rowIsometryInclAt₀}\,K\,w$ and the representation $\tau.\rho$. Let $x_0 \in \mathrm{GL}_2(\mathbb{A}_K)$ and $m \in \mathbb{Z}$ be such that $f(x_0 \cdot \mathtt{archCircleAt}\,hw\,\zeta) = \zeta^m f(x_0)$ for every unit $\zeta \in \mathbb{C}$ with $\lVert\zeta\rVert = 1$, where $\mathtt{archCircleAt}\,hw\,\zeta$ is the image of $\mathrm{diag}(\zeta,\zeta^{-1})$ in $\mathrm{GL}_2(\mathbb{A}_K)$ under the embedding of $\mathrm{GL}_2(\mathbb{C})$ at $w$. If $f(x_0) \neq 0$, then $|m| \le n_0$.
--
--   This is a pointwise form of the weight window for a finite family of archimedean types: the circle weights that can occur along the torus through a single point, at a complex place, are bounded uniformly in the place, the function and the point. Only the values of $f$ on the circle $x_0\,\mathrm{diag}(\zeta,\zeta^{-1})_w$ enter, and no smoothness is assumed; the bound is used in the weight estimate for induced sections and in the bound for the analytically continued Weyl intertwining integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_abs_le_of_apply_mul_archCircleAt_eq_zpow_mul_of_mem_iSup_archTypeSubmoduleAt.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_abs_le_of_apply_mul_archCircleAt_eq_zpow_mul_of_mem_iSup_archTypeSubmoduleAt
    (K : Type) [Field K] [NumberField K]
    (tys : ArchTypeFamily K) :
    ∃ n₀ : ℕ,
      ∀ (w : InfinitePlace K) (hw : w.IsComplex) (f : AdelicGL2 (𝓞 K) K → ℂ),
        Continuous f → f ∈ (⨆ i : Fin (tys.card w), archTypeSubmoduleAt K w (tys.rep w i)) →
        ∀ (x₀ : AdelicGL2 (𝓞 K) K) (m : ℤ),
          (∀ ζ : ℂˣ, ‖(ζ : ℂ)‖ = 1 → f (x₀ * archCircleAt hw ζ) = (ζ : ℂ) ^ m * f x₀) →
          f x₀ ≠ 0 → |m| ≤ (n₀ : ℤ) := by sorry
