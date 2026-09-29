-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_norm_whittakerCoefficient_diagOne_mul_le_ideleNorm_rpow_mul_prod_min_of_isCuspConstituent_mul_of_glArch_eq_one_of_forall_isReal
-- name    : AutomorphicForm.CuspidalConstituent.exists_norm_whittakerCoefficient_diagOne_mul_le_ideleNorm_rpow_mul_prod_min_of_isCuspConstituent_mul_of_glArch_eq_one_of_forall_isReal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/1e9cbe88-bc1a-5b6f-90b6-7a4ba13b2887
-- title:
--   Whittaker decay on the torus for totally real fields
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers with $0<c$, $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$; write $D=\bigcup_{x\in T}\{gx: g\in\mathfrak{S}\}$, where $\mathfrak{S}=$ `centreCutSiegelSet K c u d₁ d₂` consists of those $g$ whose finite part lies in the integral subgroup $\mathrm{GL}_2(\widehat{\mathcal O_K})$ and whose archimedean component at every infinite place $w$ has local height $\ge c$, window $x$-coordinate squared $\le u^2$ and determinant norm in $[d_1,d_2]$. Assume $D$ covers modulo the centre: every $g\in\mathrm{GL}_2(\mathbb{A}_K)$ can be written with $\gamma g z\in D$ for some $\gamma\in\mathrm{GL}_2(K)$ and some central idelic scalar $z$. Fix the carrier data `productionPinsOf` on $D$ with level groups $U(N)=\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, the standard Hecke generators at the finite places, and the adelic box (the measure on $\mathbb{A}_K$ being additive Haar conditioned on that box); its central subgroup is all of $\mathbb{A}_K^\times$, so $\xi$ is a homomorphism $\mathbb{A}_K^\times\to\mathbb{C}^\times$. Let $N\neq 0$ be an ideal of $\mathcal O_K$, let `tys` be a family assigning to each infinite place $w$ finitely many finite-dimensional representations of the determinant-one row-isometry subgroup of $\mathrm{GL}_2(K_w)$, and let $V$ be a cuspidal constituent for $\xi$: a non-zero subspace of the $K$-finite cuspidal space that is stable under right translation by $\ker(\mathrm{glArch})$ and by the row-isometry subgroups at the infinite places, stable under right convolution by factorizable archimedean-bi-finite test functions, and minimal with these properties. Assume every infinite place of $K$ is real. Let $x$ lie in $V$, be right invariant under $U(N)$, and lie in the archimedean cut submodule of `tys` (at each $w$, a sum of the type submodules of the listed representations). Let $w_0\in\mathbb{R}$ satisfy $\|\xi(z)\|=\|z\|_{\mathbb{A}}^{w_0}$ for all ideles $z$, and let $g$ be purely finite, i.e. $\mathrm{glArch}(g)=1$. Then there are $\delta>0$ and $C\in\mathbb{R}$ such that for every purely archimedean $k$ (that is, $\mathrm{glFin}(k)=1$) whose component at each infinite place $w$ is a row isometry (determinant of norm $1$ and the induced row map preserving $\|{\cdot}\|^2+\|{\cdot}\|^2$), and every idele $a$ with trivial finite part,
--   $$\left\|W\big(\mathrm{diag}(a,1)\,k\,g\big)\right\|\le C\prod_{w\mid\infty}\Big(\|a_w\|^{\,\mathrm{mult}(w)\,w_0/2}\,(\min(1,\|a_w\|))^{\delta}\Big),$$ where $W(h)=\int x(u(t)h)\,\psi_K(-t)\,d\nu(t)$ is the Whittaker coefficient of $x$ at $\alpha=1$ with respect to the standard additive character $\psi_K$ of $\mathbb{A}_K$ and the box-conditioned measure $\nu$, $u(t)$ denoting the unipotent matrix with upper entry $t$.
--
--   This is the classical asymptotic decay of the Whittaker function of a cusp form along the split torus $\mathrm{diag}(a,1)$ (Jacquet–Langlands), here in adelic form, place-by-place in the archimedean coordinates of $a$, uniform over the archimedean row-isometry subgroup and for a fixed finite-adelic translate $g$. It is the totally real case of the corresponding bound for a general number field, which is deduced from it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_norm_whittakerCoefficient_diagOne_mul_le_ideleNorm_rpow_mul_prod_min_of_isCuspConstituent_mul_of_glArch_eq_one_of_forall_isReal.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
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

theorem AutomorphicForm.CuspidalConstituent.exists_norm_whittakerCoefficient_diagOne_mul_le_ideleNorm_rpow_mul_prod_min_of_isCuspConstituent_mul_of_glArch_eq_one_of_forall_isReal
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
    (hreal : ∀ v : InfinitePlace K, v.IsReal)
    (x : AdelicGL2 (𝓞 K) K → ℂ)
    (hx : x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (g : AdelicGL2 (𝓞 K) K) (hg : glArch (𝓞 K) K g = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
      ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
        ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
          ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
              (diagOne a * k * g)‖ ≤ C * ∏ w : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
                (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δ) := by sorry
