-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional_of_isCompact
-- name    : AutomorphicForm.exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/b0aa2a6a-5823-5aa7-a3e0-1020ced49ba9
-- title:
--   Approximate identity of level-spherical flat test functions at compact level
-- statement:
--   Let $F$ be a number field and write $G = \mathrm{GL}_2(\mathbb{A}_F)$ for `AdelicGL2 (𝓞 F) F`. Let $U \le G$ be a subgroup whose underlying set is compact, let $O \le G$ be a subgroup whose underlying set is open, and suppose $U = O \cap \ker(\mathrm{glArch})$, the second factor being the subgroup of adelic matrices with trivial archimedean component. Let $tys$ be an archimedean type family for $F$, that is, a finite list $\mathrm{rep}\,w$ of finite-dimensional complex representations of the determinant-one row-isometry subgroup of $\mathrm{GL}_2(F_w)$ for each infinite place $w$, let $\sigma \in \mathbb{R}$, and let $Y$ be a finite-dimensional $\mathbb{C}$-subspace of the functions $G \to \mathbb{C}$ all of whose members are continuous, satisfy $y(gk) = y(g)$ for all $g \in G$, $k \in U$, and lie in $\bigsqcap_{w} \bigsqcup_{i}$ `archTypeSubmoduleAt F w (tys.rep w i)`, the intersection over infinite places of the sums of the type submodules attached to the listed representations. Then there is a sequence $f : \mathbb{N} \to (G \to \mathbb{C})$ such that each $f_n$ is a factorizable test function (a product $f_n(g) = f_a(\mathrm{glArch}\,g)\, f_f(\mathrm{glFin}\,g)$ with $f_a$ smooth in the mixed-space matrix entries and compactly supported, and $f_f$ locally constant and compactly supported), is level-spherical of type $tys$ at $U$ (its archimedean factor is an archimedean test factor, is bi-finite for $tys$ in the sense of `IsArchFactorBiFinite`, and is invariant under conjugation by $\mathrm{archRowIsometryInclAt₀}\,F\,w\,k$ for every infinite place $w$ and every determinant-one row isometry $k$ over $F_w$, while its finite factor is the indicator of the image $\mathrm{glFin}(U)$), and is fixed by the $\sigma$-flat operation, i.e. $f_n(y) = \overline{f_n(y^{-1})}\,\lVert \det y\rVert_{\mathbb{A}}^{-\sigma}$; and such that for every $y \in Y$ and every $g \in G$ the right convolutions $\int_G y(gx) f_n(x)\,d\mu(x)$, taken against the adelic Haar measure on $G$, converge to $y(g)$ as $n \to \infty$.
--
--   This supplies an approximate identity inside the algebra of factorizable test functions which is adapted simultaneously to a compact level $U$ cut out of an open subgroup by the finite-adelic subgroup, to a prescribed family of archimedean types, and to the $\sigma$-flat symmetry, so that right convolution by the members of the sequence recovers each element of a given finite-dimensional typed space of right-$U$-invariant functions. It is the general-level form of the corresponding statement for principal levels, and is used to produce test functions whose right convolution acts injectively, and eventually as the identity, on finite-dimensional spaces of cuspidal constituents.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional_of_isCompact.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchSpherical

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional_of_isCompact
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : AutomorphicForm.ArchTypeFamily F) (σ : ℝ)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hY : FiniteDimensional ℂ ↥Y)
    (hYc : ∀ y ∈ Y, Continuous y)
    (hYU : ∀ y ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, y (g * k) = y g)
    (hYt : Y ≤ archCutSubmodule F tys) :
    ∃ f : ℕ → (AdelicGL2 (𝓞 F) F → ℂ),
      (∀ n, IsFactorizableTestFn F (f n) ∧
        IsLevelSphericalOfType F tys U (f n) ∧
        flat F σ (f n) = f n) ∧
      ∀ y ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F,
        Filter.Tendsto (fun n => rightConv F y (f n) g) Filter.atTop (nhds (y g)) := by sorry
