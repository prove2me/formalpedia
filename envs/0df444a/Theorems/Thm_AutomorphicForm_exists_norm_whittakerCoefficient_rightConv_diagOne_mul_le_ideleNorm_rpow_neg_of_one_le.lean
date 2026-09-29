-- Prove2me | Theorems.Thm_AutomorphicForm_exists_norm_whittakerCoefficient_rightConv_diagOne_mul_le_ideleNorm_rpow_neg_of_one_le
-- name    : AutomorphicForm.exists_norm_whittakerCoefficient_rightConv_diagOne_mul_le_ideleNorm_rpow_neg_of_one_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/495e75b9-4a1d-5acc-ad85-2c3103a49bf8
-- title:
--   Rapid decay of the first Whittaker coefficient of a smoothed cusp form
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Write $D=\bigcup_{x\in T}\{g x : g\in S\}$, where $S$ is the centre-cut Siegel set of $g$ whose finite part lies in $\mathrm{GL}_2(\widehat{\mathcal O_K})$, whose archimedean component at every infinite place $w$ has local height $\ge c$, window quantity $\mathrm{xWindowSq}\le u^2$ and determinant norm in $[d_1,d_2]$; assume $D$ covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo the centre, i.e. every $g$ can be moved into $D$ by left multiplication by a point of $\mathrm{GL}_2(K)$ and right multiplication by a central idelic scalar. Let `pins` be `productionPinsOf` for the window $D$, the level groups $N\mapsto \mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, the Hecke generators $v\mapsto \mathrm{heckeGen}(v)$ and the box `adelicBox K`; its central group is all of $(\mathbb{A}_K)^\times$, its measure on $\mathrm{GL}_2(\mathbb{A}_K)$ is the Borel Haar measure, and its measure on $\mathbb{A}_K$ is additive Haar measure conditioned on `adelicBox K`. Let $\chi$ be a character of that central group, and let $\varphi:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous and a cusp automorphic function for `pins` and $\chi$ (an `LsXiMemberAt` member whose constant term along the unipotent subgroup $x\mapsto\begin{pmatrix}1&x\\0&1\end{pmatrix}$ vanishes identically). Let $f$ be a factorizable test function, i.e. $f(g)=f_\infty(\mathrm{glArch}\,g)\,f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with $f_\infty$ given by a smooth function of the matrix entries and compactly supported, and $f_{\mathrm{fin}}$ locally constant with compact support. Let `tys` be a family assigning to each infinite place $w$ finitely many representations of the row-isometry subgroup at $w$, and assume the right convolution $\varphi * f$ lies in the corresponding archimedean cut submodule, the infimum over $w$ of the sums of the associated type submodules. Let $w_0\in\mathbb{R}$ with $\|\chi(z)\|=\|z\|^{w_0}$ for every idele $z$, where $\|\cdot\|$ is the idele norm given by the distributive Haar character. Then for every $m\in\mathbb{N}$ there is a constant $C$ such that for all $k\in\mathrm{GL}_2(\mathbb{A}_K)$ with trivial finite part and with archimedean component at each infinite place a row isometry (determinant of norm $1$, rows preserving the sum of squared norms), and all ideles $a$ with finite component $1$ and $\|a\|\ge 1$, the Whittaker coefficient of $\varphi * f$ for the standard additive character and $\alpha=1$, evaluated at $\mathrm{diag}(a,1)\,k$, has norm at most $C\,\|a\|^{-m}$.
--
--   This is the rapid decay, to every polynomial order and uniformly over the archimedean row-isometry subgroup, of the first Whittaker function of a cusp form smoothed by a factorizable test function, on the part of the torus where the idele norm is at least $1$. It controls the large-torus end of the archimedean zeta integrals attached to $\varphi * f$ and is used in the estimates for class sums and for window masses of isotypic cusp functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_norm_whittakerCoefficient_rightConv_diagOne_mul_le_ideleNorm_rpow_neg_of_one_le.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain

theorem AutomorphicForm.exists_norm_whittakerCoefficient_rightConv_diagOne_mul_le_ideleNorm_rpow_neg_of_one_le
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (χ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsCuspAutomorphicFnAt K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) χ φ)
    (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f)
    (tys : AutomorphicForm.ArchTypeFamily K) (hxt : rightConv K φ f ∈ archCutSubmodule K tys)
    (w₀ : ℝ) (hχ : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ideleNorm K z ^ w₀)
    (m : ℕ) :
    ∃ C : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
      (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → 1 ≤ ideleNorm K a →
        ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K φ f) 1
            (diagOne a * k)‖ ≤ C * ideleNorm K a ^ (-(m : ℝ)) := by sorry
