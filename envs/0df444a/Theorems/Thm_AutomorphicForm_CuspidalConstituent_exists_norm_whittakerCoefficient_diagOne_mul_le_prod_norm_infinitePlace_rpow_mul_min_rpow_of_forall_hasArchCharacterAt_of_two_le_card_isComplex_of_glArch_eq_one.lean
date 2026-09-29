-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_norm_whittakerCoefficient_diagOne_mul_le_prod_norm_infinitePlace_rpow_mul_min_rpow_of_forall_hasArchCharacterAt_of_two_le_card_isComplex_of_glArch_eq_one
-- name    : AutomorphicForm.CuspidalConstituent.exists_norm_whittakerCoefficient_diagOne_mul_le_prod_norm_infinitePlace_rpow_mul_min_rpow_of_forall_hasArchCharacterAt_of_two_le_card_isComplex_of_glArch_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/b72d6581-a012-53c5-8227-2238ebbf2e73
-- title:
--   Archimedean decay of torus Whittaker coefficients, two complex places
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $c>0$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Write $D=\bigcup_{x\in T}\,(\cdot\,x)\,[\,\mathrm{centreCutSiegelSet}\,K\,c\,u\,d_1\,d_2\,]$, the union of the right translates by the elements of $T$ of the set of $g$ whose finite component is integral, whose archimedean components have local height at least $c$ and $x$-window at most $u^2$ at every infinite place, and whose archimedean determinant norms all lie in $[d_1,d_2]$; assume $D$ covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo global points on the left and central ideles on the right. Let `pins` be the production carrier data on $D$ with level groups $U(\mathfrak{N})=\mathrm{levelOne}(\mathfrak{N})\cap\ker(\mathrm{glArch})$, Hecke generators $\mathrm{heckeGen}$, adelic Haar measures, central group $\top$, and adelic additive measure conditioned on the box $\mathrm{adelicBox}\,K$, and let $\xi$ be a character of the idele units. Let $\mathfrak{N}\neq 0$ be an ideal of $\mathcal{O}_K$, `tys` an archimedean type family, and $V$ a submodule of the complex-valued functions on $\mathrm{GL}_2(\mathbb{A}_K)$ which is a cuspidal constituent for `pins` and $\xi$: a nonzero cuspidal $K$-finite subrepresentation stable under right translation by the finite subgroup and by the row-isometry groups at the infinite places and under the relevant right convolutions, and minimal among such subrepresentations. Let $y$ lie in $V$, be right invariant under $U(\mathfrak{N})$, and lie in the archimedean cut submodule of types `tys`. Assume that at every real place $w$ there is $n\in\mathbb{Z}$ with $\mathrm{HasArchCharacterAt}_0$ holding for $y$ at $w$ with the character $\mathrm{archWeightCharAt}\,h_w\,n$, the $n$-th power of the standard weight-one character of the row-isometry group at $w$; assume $K$ has two distinct complex places; assume $|\xi(z)|=\|z\|^{w_0}$ for all ideles $z$, where $\|\cdot\|$ is the idele norm given by the Haar modulus and $w_0\in\mathbb{R}$; and let $g\in\mathrm{GL}_2(\mathbb{A}_K)$ have trivial archimedean component. Then there are $\delta>0$ and $C\in\mathbb{R}$ such that for every idele unit $a$ whose finite component is $1$, the Whittaker coefficient of $y$ at $\alpha=1$ with respect to the standard additive character, evaluated at $\mathrm{diagOne}(a)\,g$, satisfies $$\bigl\|W(y)(\mathrm{diagOne}(a)g)\bigr\|\le C\prod_{w\mid\infty}\|a_w\|^{m_w w_0/2}\,\min(1,\|a_w\|)^{\delta},$$ with $m_w$ the multiplicity (local degree) of $w$ and $a_w$ the $w$-component of the archimedean part of $a$.
--
--   This is the archimedean size estimate for the Whittaker function of a pure-weight, level-$\mathfrak{N}$ vector in a cuspidal constituent, restricted to the diagonal torus and twisted by a fixed translate with trivial archimedean component: a power of each archimedean absolute value matching the central character, with a uniform extra decay exponent $\delta$ as the coordinates tend to zero. It feeds the corresponding bound in terms of the global idele norm times a product of minima, used in the analytic control of Whittaker expansions of automorphic forms on $\mathrm{GL}_2$ over fields with at least two complex places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_norm_whittakerCoefficient_diagOne_mul_le_prod_norm_infinitePlace_rpow_mul_min_rpow_of_forall_hasArchCharacterAt_of_two_le_card_isComplex_of_glArch_eq_one.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.exists_norm_whittakerCoefficient_diagOne_mul_le_prod_norm_infinitePlace_rpow_mul_min_rpow_of_forall_hasArchCharacterAt_of_two_le_card_isComplex_of_glArch_eq_one
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily K)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (hpure : ∀ (w : InfinitePlace K) (hw : w.IsReal), ∃ n : ℤ, HasArchCharacterAt₀ K w (archWeightCharAt hw n) y)
    (h2 : ∃ w w' : InfinitePlace K, w ≠ w' ∧ w.IsComplex ∧ w'.IsComplex)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (g : AdelicGL2 (𝓞 K) K) (hg : glArch (𝓞 K) K g = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
              (diagOne a * g)‖ ≤ C * ∏ w : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
                (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δ) := by sorry
