-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isFactorizableTestFn_isBiInvariantUnder_forall_archCasimirAtComplex_convOp_eq_convOp_of_isComplex
-- name    : AutomorphicForm.exists_isFactorizableTestFn_isBiInvariantUnder_forall_archCasimirAtComplex_convOp_eq_convOp_of_isComplex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/331126f7-84ff-53d2-8499-af065514f4e5
-- title:
--   Complex-place Casimir operators pass onto the test function
-- statement:
--   Let $K$ be a number field, $w$ a complex infinite place of $K$, and $U$ a subgroup of $GL_2(\mathbb{A}_K)$ contained in `finiteAdelicGL2Subgroup K`, the kernel of the archimedean projection $GL_2(\mathbb{A}_K)\to GL_2(K\otimes\mathbb{R})$. Let $f:GL_2(\mathbb{A}_K)\to\mathbb{C}$ be a factorizable test function, i.e. $f(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$ where $f_\infty$ is compactly supported and given by a function of the matrix entries that is $C^\infty$ over $\mathbb{R}$ on the mixed space, and $f_{\mathrm{fin}}$ is locally constant with compact support; assume further that $f(ug)=f(g)=f(gu)$ for all $u\in U$ and all $g$. Then there exist $\beta,\bar\beta:GL_2(\mathbb{A}_K)\to\mathbb{C}$, again factorizable test functions bi-invariant under $U$ in the same sense, such that for every continuous $x:GL_2(\mathbb{A}_K)\to\mathbb{C}$ the right convolution $(\mathrm{convOp}\,f)(x):g\mapsto\int x(gy)f(y)\,dy$ against the adelic Haar measure satisfies: for each $g$ the map $e\mapsto (\mathrm{convOp}\,f)(x)(g\cdot\mathrm{archComplexLiftAt}\,e)$ is $C^\infty$ over $\mathbb{R}$ on the invertible complex $2\times 2$ matrices, and the two Casimir operators at $w$, formed from the holomorphic respectively antiholomorphic Wirtinger combinations of the archimedean directional derivatives in the directions $H,E,F$, send $(\mathrm{convOp}\,f)(x)$ to $(\mathrm{convOp}\,\beta)(x)$ and $(\mathrm{convOp}\,\bar\beta)(x)$ respectively. Note that $\beta$ and $\bar\beta$ are chosen uniformly in $x$.
--
--   This is the complex-place form of the standard device by which a differential operator applied to a convolution $x*f$ is transferred to the test function, the Casimir operators of $GL_2(\mathbb{C})$ at $w$ being replaced by the holomorphic and antiholomorphic left Casimirs of $f$; the statement is packaged so as to be independent of the level subgroup $U$ and of any automorphy type. It feeds the estimate for orthonormal families in isotypic cuspidal subspaces on which the Casimir acts by a scalar, and relies on the corresponding first-order statement for single archimedean derivatives together with the continuity and compact support of factorizable test functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isFactorizableTestFn_isBiInvariantUnder_forall_archCasimirAtComplex_convOp_eq_convOp_of_isComplex.lean

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

theorem AutomorphicForm.exists_isFactorizableTestFn_isBiInvariantUnder_forall_archCasimirAtComplex_convOp_eq_convOp_of_isComplex
    (K : Type) [Field K] [NumberField K] (w : InfinitePlace K) (hw : w.IsComplex)
    (U : Subgroup (AdelicGL2 (𝓞 K) K)) (hU : U ≤ finiteAdelicGL2Subgroup K)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hff : IsFactorizableTestFn K f) (hfU : IsBiInvariantUnder K U f) :
    ∃ β βb : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K β ∧ IsBiInvariantUnder K U β ∧
      IsFactorizableTestFn K βb ∧ IsBiInvariantUnder K U βb ∧
      ∀ x : AdelicGL2 (𝓞 K) K → ℂ, Continuous x →
        IsArchSmoothAtComplex hw (convOp K f x) ∧
        archCasimirAtComplex hw (convOp K f x) = convOp K β x ∧
        archCasimirBarAtComplex hw (convOp K f x) = convOp K βb x := by sorry
