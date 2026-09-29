-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_norm_whittakerCoefficient_diagOne_mul_le_min_norm_infinitePlace_rpow_of_isComplex_of_glArch_eq_one
-- name    : AutomorphicForm.CuspidalConstituent.exists_norm_whittakerCoefficient_diagOne_mul_le_min_norm_infinitePlace_rpow_of_isComplex_of_glArch_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/e8a0b589-fd0c-5ff6-8dfa-aed1ebafe610
-- title:
--   Power bound at a complex place for torus Whittaker coefficients
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers with $c>0$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Write $D=\bigcup_{x\in T}\,(\cdot\,x)$-image of the centre-cut Siegel set with parameters $c,u,d_1,d_2$ (those $g$ whose finite part is integral, whose archimedean components at every infinite place have local height at least $c$ and window coordinate $\mathrm{xWindowSq}\le u^2$, and whose archimedean determinant norm at every infinite place lies in $[d_1,d_2]$), and assume that $D$ covers modulo the centre: every $g\in\mathrm{GL}_2(\mathbb{A}_K)$ satisfies $\gamma g z\in D$ for some $\gamma\in\mathrm{GL}_2(K)$ and some central scalar idele $z$. The carrier data are the production pins on $D$ with level subgroups $U(\mathfrak{N})=\mathrm{levelOne}(\mathfrak{N})\cap\ker(\mathrm{glArch})$, Hecke generators $\mathrm{heckeGen}$ at the finite places, Haar measures on $\mathrm{GL}_2(\mathbb{A}_K)$ and the conditional additive Haar measure on the adelic box, and central subgroup $Z=\mathbb{A}_K^\times$. Let $\xi:\mathbb{A}_K^\times\to\mathbb{C}^\times$ be a character, $\mathfrak{N}\neq 0$ an ideal of $\mathcal{O}_K$, $\mathrm{tys}$ a family of archimedean types, and $V$ a submodule of $\mathbb{C}$-valued functions on $\mathrm{GL}_2(\mathbb{A}_K)$ which is a cuspidal constituent for these pins and $\xi$ (a nonzero cuspidal subrepresentation that is minimal among such). Let $y$ lie in $V$, be right invariant under $U(\mathfrak{N})$, and lie in $\bigsqcap_{w'}\bigsqcup_i$ of the archimedean type submodules prescribed by $\mathrm{tys}$. Let $w_0$ be real with $\lVert\xi(z)\rVert=\lVert z\rVert_{\mathbb{A}}^{w_0}$ for all ideles $z$, where $\lVert\cdot\rVert_{\mathbb{A}}$ is the idele norm given by the distributive Haar character. Let $w$ be a complex infinite place of $K$, let $b$ be an idele whose finite component is $1$, and let $g\in\mathrm{GL}_2(\mathbb{A}_K)$ have trivial archimedean component. Then there exist $\delta>0$ and a constant $C$ such that for every idele $a$ with trivial finite component and $a_{w'}=b_{w'}$ at every infinite place $w'\neq w$, the Whittaker coefficient of $y$ at $\alpha=1$ with respect to the standard additive character, evaluated at $\mathrm{diag}(a,1)\,g$, satisfies $$\lVert W(y)(\mathrm{diag}(a,1)g)\rVert\le C\,\lVert a_w\rVert^{\,\mathrm{mult}(w)\,w_0/2}\,\bigl(\min(1,\lVert a_w\rVert)\bigr)^{\delta},$$ the exponent $\mathrm{mult}(w)\,w_0/2$ being $w_0$ since $w$ is complex.
--
--   This is the one-variable archimedean estimate at a complex place for the torus Whittaker function of a level-and-type cut vector in a cuspidal constituent of $\mathrm{GL}_2$ over a number field, allowing an arbitrary right translate by an element with trivial archimedean component: boundedness for large $\lVert a_w\rVert$ and decay by a positive power as $\lVert a_w\rVert\to 0$, with the remaining archimedean coordinates frozen at those of $b$. It feeds the statements that assemble such bounds into products over all infinite places and into idele-norm bounds for the Whittaker function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_norm_whittakerCoefficient_diagOne_mul_le_min_norm_infinitePlace_rpow_of_isComplex_of_glArch_eq_one.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
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

theorem AutomorphicForm.CuspidalConstituent.exists_norm_whittakerCoefficient_diagOne_mul_le_min_norm_infinitePlace_rpow_of_isComplex_of_glArch_eq_one
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
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (b : (AdeleRing (𝓞 K) K)ˣ) (hb : ((b : AdeleRing (𝓞 K) K)).2 = 1)
    (g : AdelicGL2 (𝓞 K) K) (hg : glArch (𝓞 K) K g = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        (∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
        ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
              (diagOne a * g)‖ ≤ C * ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
            (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δ := by sorry
