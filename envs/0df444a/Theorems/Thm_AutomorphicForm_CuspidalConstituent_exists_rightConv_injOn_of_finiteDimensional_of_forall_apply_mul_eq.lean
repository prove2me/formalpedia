-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_rightConv_injOn_of_finiteDimensional_of_forall_apply_mul_eq
-- name    : AutomorphicForm.CuspidalConstituent.exists_rightConv_injOn_of_finiteDimensional_of_forall_apply_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/7811c788-8bd3-50fa-baac-f594550bce03
-- title:
--   A single level-spherical flat test function separating Y
-- statement:
--   Let $F$ be a number field, and work with $G = \mathrm{GL}_2(\mathbb{A}_F)$, realised as `AdelicGL2 (𝓞 F) F`, the general linear group of degree $2$ over the adele ring of $F$, with its Borel $\sigma$-algebra and the Haar measure `adelicGLHaar`. Let $U \le G$ be a subgroup whose underlying set is compact, let $O \le G$ be a subgroup whose underlying set is open, and assume $U = O \sqcap \ker(\mathrm{glArch})$, the intersection of $O$ with the finite-adelic subgroup `finiteAdelicGL2Subgroup F`. Let `tys` be an archimedean type family (for each infinite place $w$ of $F$, a finite list of finite-dimensional complex representations of the row-isometry subgroup of $\mathrm{GL}_2(F_w)$), let $\sigma \in \mathbb{R}$, and let $Y$ be a $\mathbb{C}$-submodule of the functions $G \to \mathbb{C}$ that is finite-dimensional, consists of continuous functions, satisfies $y(gk) = y(g)$ for all $g \in G$ and $k \in U$, and is contained in `archCutSubmodule F tys`, the intersection over all infinite places $w$ of the sum of the type submodules attached to the representations `tys.rep w i`. Then there exists $f : G \to \mathbb{C}$ which (i) is a factorisable test function, i.e. $f(g) = f_\infty(\mathrm{glArch}\,g)\, f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with $f_\infty$ given by a smooth function of the archimedean matrix entries and compactly supported, and $f_{\mathrm{fin}}$ locally constant and compactly supported; (ii) is level-spherical of type `tys` at $U$, i.e. $f(g) = f_\infty(\mathrm{glArch}\,g)$ times the indicator of the image of $U$ under $\mathrm{glFin}$ evaluated at $\mathrm{glFin}\,g$, for some archimedean test factor $f_\infty$ which is bi-finite for `tys` and invariant under conjugation by row isometries at each infinite place; (iii) satisfies $\mathrm{flat}_\sigma f = f$, where $(\mathrm{flat}_\sigma f)(y) = \overline{f(y^{-1})}\,\|\det y\|^{-\sigma}$; and (iv) separates $Y$: for every $y \in Y$, if the right convolution $g \mapsto \int_G y(gx) f(x)\,dx$ vanishes identically, then $y = 0$.
--
--   This is the smoothing step that provides one test function acting injectively on a prescribed finite-dimensional space of continuous, right-$U$-invariant, typed functions on $\mathrm{GL}_2(\mathbb{A}_F)$, with the test function constrained to be level-spherical at the compact level $U$ and symmetric for the $\sigma$-flat involution. It is used in the proof that a cuspidal subcarrier contained in the $K$-finite cusp submodule and generating an irreducible cuspidal subrepresentation is finite-dimensional.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_rightConv_injOn_of_finiteDimensional_of_forall_apply_mul_eq.lean

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

theorem AutomorphicForm.CuspidalConstituent.exists_rightConv_injOn_of_finiteDimensional_of_forall_apply_mul_eq
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : AutomorphicForm.ArchTypeFamily F) (σ : ℝ)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hY : FiniteDimensional ℂ ↥Y)
    (hYc : ∀ y ∈ Y, Continuous y)
    (hYU : ∀ y ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, y (g * k) = y g)
    (hYt : Y ≤ archCutSubmodule F tys) :
    ∃ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f ∧
      IsLevelSphericalOfType F tys U f ∧
      flat F σ f = f ∧
      ∀ y ∈ Y, rightConv F y f = 0 → y = 0 := by sorry
