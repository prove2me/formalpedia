-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_whittakerCoefficient_diagOne_mul_eq_sum_mul_of_isComplex_of_glArch_eq_one
-- name    : AutomorphicForm.CuspidalConstituent.exists_forall_whittakerCoefficient_diagOne_mul_eq_sum_mul_of_isComplex_of_glArch_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/87ea8efa-f6ef-5e96-8c9b-e8c6251939e9
-- title:
--   Finite rank in one complex variable of Whittaker coefficients
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $c>0$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$ such that $D=\bigcup_{x\in T}\{h x: h\in \mathrm{centreCutSiegelSet}(c,u,d_1,d_2)\}$ covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo the centre, i.e. every $g$ can be written with $\gamma g z\in D$ for some $\gamma\in \mathrm{GL}_2(K)$ and some idele $z$ acting by the central scalar. Work with the carrier data `productionPinsOf` attached to $D$, to the level subgroups $U(\mathfrak{N})=\mathrm{levelOne}(\mathfrak{N})\cap\ker(\mathrm{glArch})$, to the Hecke generators $\mathrm{heckeGen}(v)$ and to the box $\mathrm{adelicBox}(K)$ (whose group $Z$ is the full idele unit group, whose measures are the adelic Haar measures and whose additive measure is conditioned on the box). Let $\xi\colon Z\to\mathbb{C}^\times$ be a character, $\mathfrak{N}\neq 0$ an ideal of $\mathcal{O}_K$, $\mathrm{tys}$ an archimedean type family, and let $V$ be a cuspidal constituent for $\xi$ in the sense of `IsCuspConstituent`: a nonzero submodule of $K$-finite cusp functions, stable under right translation by finite-adelic elements and by the archimedean row-isometry subgroups and under right convolution by factorizable archimedean bi-finite test functions, and minimal among such submodules. Let $y$ lie in $V$, be right invariant under all $U(\mathfrak{N})$, and lie in $\mathrm{archCutSubmodule}(\mathrm{tys})$. Assume $\|\xi(z)\|=\|z\|_{\mathbb{A}}^{w_0}$ for all ideles $z$, where $\|\cdot\|_{\mathbb{A}}$ is the idele norm given by the module of the Haar measure. Let $w$ be a complex infinite place and $g\in\mathrm{GL}_2(\mathbb{A}_K)$ with trivial archimedean component, $\mathrm{glArch}(g)=1$. Then there are $d\in\mathbb{N}$ and functions $\varphi_1,\dots,\varphi_d\colon K_w\to\mathbb{C}$ such that for every idele $b$ with trivial finite component there are constants $c_1(b),\dots,c_d(b)\in\mathbb{C}$ with the property that for every idele $a$ with trivial finite component whose component at each infinite place $w'\neq w$ equals that of $b$, the Whittaker coefficient of $y$ at $\alpha=1$ with respect to the standard additive character, namely $\int y(u(x)\,\mathrm{diag}(a,1)g)\,\psi(-x)\,d\nu(x)$ with $\nu$ the box-conditioned adelic measure, equals $\sum_{k}c_k(b)\varphi_k(a_w)$.
--
--   This is the finiteness half of the analysis of Whittaker functions of a cuspidal constituent of $\mathrm{GL}_2$ at a single complex place: the Whittaker coefficient, restricted to the diagonal torus with the coordinates away from $w$ frozen, spans a finite-dimensional space of functions of the variable at $w$, with no decay or unitarity asserted. It feeds the quantitative estimate for Whittaker coefficients at places with at least two complex places among the archimedean characters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_forall_whittakerCoefficient_diagOne_mul_eq_sum_mul_of_isComplex_of_glArch_eq_one.lean

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

theorem AutomorphicForm.CuspidalConstituent.exists_forall_whittakerCoefficient_diagOne_mul_eq_sum_mul_of_isComplex_of_glArch_eq_one
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
    (g : AdelicGL2 (𝓞 K) K) (hg : glArch (𝓞 K) K g = 1) :
    ∃ (d : ℕ) (φ : Fin d → w.Completion → ℂ),
      ∀ b : (AdeleRing (𝓞 K) K)ˣ, ((b : AdeleRing (𝓞 K) K)).2 = 1 → ∃ cb : Fin d → ℂ,
        ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
          (∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
          whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
              (diagOne a * g) = ∑ k, cb k * φ k (((a : AdeleRing (𝓞 K) K)).1 w) := by sorry
