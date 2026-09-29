-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isFactorizableTestFn_isBiInvariantUnder_forall_archCasimirAt_convOp_eq_convOp_of_isReal
-- name    : AutomorphicForm.exists_isFactorizableTestFn_isBiInvariantUnder_forall_archCasimirAt_convOp_eq_convOp_of_isReal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/79cc96c8-3303-5a6f-a812-d158806eaaa6
-- title:
--   Casimir at a real place passes onto the test function
-- statement:
--   Let $K$ be a number field and $w$ an infinite place of $K$ with $w$ real, and let $U$ be a subgroup of $\mathrm{GL}_2(\mathbb{A}_K)$ contained in `finiteAdelicGL2Subgroup K`, the kernel of the archimedean projection $\mathrm{GL}_2(\mathbb{A}_K) \to \mathrm{GL}_2(K \otimes \mathbb{R})$. Let $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be factorizable in the sense that $f(g) = f_\infty(\mathrm{glArch}\,g)\, f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with $f_\infty$ of compact support and of the form $\Phi$ composed with the matrix entries for some $C^\infty$ function $\Phi$ on the mixed space, and $f_{\mathrm{fin}}$ locally constant of compact support; assume further that $f(ug) = f(g) = f(gu)$ for all $u \in U$ and all $g$. Then there is a function $\beta$ with the same two properties (factorizable of this shape, and bi-invariant under $U$) such that for every continuous $x : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ the right convolution $(x * f)(g) = \int x(gy) f(y)\,dy$ against the adelic Haar measure satisfies: for every $g$ the map $e \mapsto (x*f)(g \cdot \mathrm{archRealLiftAt}\,hw\,e)$ on $2 \times 2$ real matrices is $C^\infty$ on the locus of nonzero determinant, and $\mathrm{archCasimirAt}\,hw\,(x*f) = x * \beta$, where $\mathrm{archCasimirAt}$ is $-\bigl(\tfrac14 D_H D_H - \tfrac12 D_H + D_E D_{F}\bigr)$ formed from the derivatives $D_d\varphi(g) = \tfrac{d}{dt}\varphi(g\,\mathrm{archFlowAt}\,hw\,d\,t)|_{t=0}$ along the one-parameter flows at $w$ in the directions $H$, $E$, $F$.
--
--   This is the statement that the Casimir operator at a real place, realised through right translations, passes through a right convolution onto the test function: convolution with a factorizable test function lands in the space of functions smooth at $w$, and applying $\Omega_w$ amounts to convolving with another factorizable test function of the same level. It is used in the estimates on $L^2$-norms of convolution operators on isotypic cuspidal subspaces, where a Casimir eigenvalue condition is converted into a statement about the convolution kernel.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isFactorizableTestFn_isBiInvariantUnder_forall_archCasimirAt_convOp_eq_convOp_of_isReal.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_isFactorizableTestFn_isBiInvariantUnder_forall_archCasimirAt_convOp_eq_convOp_of_isReal
    (K : Type) [Field K] [NumberField K] (w : InfinitePlace K) (hw : w.IsReal)
    (U : Subgroup (AdelicGL2 (𝓞 K) K)) (hU : U ≤ finiteAdelicGL2Subgroup K)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hff : IsFactorizableTestFn K f) (hfU : IsBiInvariantUnder K U f) :
    ∃ β : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K β ∧ IsBiInvariantUnder K U β ∧
      ∀ x : AdelicGL2 (𝓞 K) K → ℂ, Continuous x →
        IsArchSmoothAt hw (convOp K f x) ∧ archCasimirAt hw (convOp K f x) = convOp K β x := by sorry
