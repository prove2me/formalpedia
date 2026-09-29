-- Prove2me | Theorems.Thm_AutomorphicForm_exists_integral_rightConv_eq_rightConv
-- name    : AutomorphicForm.exists_integral_rightConv_eq_rightConv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/6bce7f39-7da0-5f5c-8b1e-cf51fba01886
-- title:
--   Averaging a right convolution over a compact level
-- statement:
--   Let $F$ be a number field and write $G = \mathrm{GL}_2(\mathbb{A}_F)$ for `AdelicGL2 (𝓞 F) F`. Let $U \le G$ be a subgroup whose underlying set is compact, let $O \le G$ be a subgroup whose underlying set is open, and assume $U = O \sqcap$ `finiteAdelicGL2Subgroup F`, the latter being the kernel of the archimedean projection $\mathrm{glArch}$, so that $U$ consists of elements with trivial archimedean component; let $\mu$ be a Haar probability measure on $U$ for its Borel structure. Let `tys` be an archimedean type family, i.e. a cardinality function $w \mapsto \mathrm{card}(w)$ on the infinite places of $F$ together with, for each $w$ and each $i < \mathrm{card}(w)$, a finite-dimensional complex representation of `rowIsometrySubgroup₀` of the completion at $w$. Let $y : G \to \mathbb{C}$ be continuous and right $U$-invariant, $y(xu) = y(x)$ for all $x \in G$, $u \in U$. Let $f : G \to \mathbb{C}$ be a factorizable test function, that is $f(g) = f_\infty(\mathrm{glArch}\,g)\, f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with $f_\infty$ compactly supported and given by a smooth function of the archimedean matrix entries, and $f_{\mathrm{fin}}$ locally constant with compact support; assume moreover that $f$ is bi-finite of type `tys`, meaning $x \mapsto f(x^{-1})$ lies in `archCutSubmodule F tys` and $f$ lies in `archDualCutSubmodule F tys`. Then there exists $f' : G \to \mathbb{C}$ which is again a factorizable test function, again bi-finite of type `tys`, is two-sided $U$-invariant ($f'(ux) = f'(x) = f'(xu)$ for all $x \in G$, $u \in U$), and satisfies, for every $x \in G$, $\int_U (y * f)(xu)\, d\mu(u) = (y * f')(x)$, where $(y * h)(g) = \int_G y(gz) h(z)\, dz$ is `rightConv` taken against the adelic Haar measure `adelicGLHaar` on $G$.
--
--   This is the smoothing step underlying the action of the Hecke algebra of level-bi-invariant test functions on the space of automorphic forms: averaging a right convolution over a compact level $U$ again has the form of a right convolution, by a test function of the same archimedean type which is bi-invariant under $U$. It is used in the analysis of cuspidal constituents, in [`AutomorphicForm.CuspidalConstituent.iInf_isCuspSubrep_inf_invariants_inf_archCutSubmodule_le`](thm.html#AutomorphicForm.CuspidalConstituent.iInf_isCuspSubrep_inf_invariants_inf_archCutSubmodule_le), [`AutomorphicForm.CuspidalConstituent.iInf_isCuspSubrep_inf_levelInvariantSubmodule_inf_archCutSubmodule_le`](thm.html#AutomorphicForm.CuspidalConstituent.iInf_isCuspSubrep_inf_levelInvariantSubmodule_inf_archCutSubmodule_le) and [`AutomorphicForm.CuspidalConstituent.inf_eq_bot_or_le_of_isCuspConstituent_principal`](thm.html#AutomorphicForm.CuspidalConstituent.inf_eq_bot_or_le_of_isCuspConstituent_principal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_integral_rightConv_eq_rightConv.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm AutomorphicForm.CuspidalConstituent
open scoped BigOperators

theorem AutomorphicForm.exists_integral_rightConv_eq_rightConv
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    [MeasurableSpace U] [BorelSpace U] (μ : Measure U) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (tys : ArchTypeFamily F)
    {y : AdelicGL2 (𝓞 F) F → ℂ} (hyc : Continuous y) (hyU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, y (x * u) = y x)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsFactorizableTestFn F f) (hbf : IsArchBiFinite F tys f) :
    ∃ f' : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f' ∧ IsArchBiFinite F tys f' ∧
      (∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, f' (u * x) = f' x ∧ f' (x * u) = f' x) ∧
      ∀ x : AdelicGL2 (𝓞 F) F, ∫ u, rightConv F y f (x * (u : AdelicGL2 (𝓞 F) F)) ∂μ = rightConv F y f' x := by sorry
