-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_norm_whittakerCoefficient_diagOne_mul_le_ideleNorm_rpow_mul_prod_min_of_isCuspConstituent_mul_of_glArch_eq_one
-- name    : AutomorphicForm.CuspidalConstituent.exists_norm_whittakerCoefficient_diagOne_mul_le_ideleNorm_rpow_mul_prod_min_of_isCuspConstituent_mul_of_glArch_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/65e914cd-7829-5f2f-9027-b6ed7f1373eb
-- title:
--   Whittaker decay at the torus origin, finite translate
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $c>0$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Put $D=\bigcup_{x\in T}\{h x : h\in \mathfrak{S}\}$, where $\mathfrak{S}$ is the set of $g$ whose finite part lies in $\mathrm{GL}_2(\widehat{\mathcal{O}}_K)$ and which satisfy, at every infinite place $w$, $\mathrm{localHeight}\ge c$, $\mathrm{xWindowSq}\le u^2$ and $\|\det\|_w\in[d_1,d_2]$; assume $D$ covers modulo the centre, i.e. every $g$ admits $\gamma\in\mathrm{GL}_2(K)$ and an idele $z$ with $\gamma g\,z\in D$. Let the carrier data be `productionPinsOf` for $D$, the level groups $\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, the Hecke generators $\mathrm{heckeGen}$ and the adelic box; its central subgroup is all of $\mathbb{A}_K^\times$, its measure on $\mathbb{A}_K$ is additive Haar conditioned on the box. Let $\xi$ be a character of that subgroup, $N\ne 0$ an ideal of $\mathcal{O}_K$, `tys` a family of representations of the row-isometry groups at the infinite places, and $V$ a cuspidal constituent for $\xi$: a non-zero subspace of the $K_\infty$-finite cuspidal space stable under right translation by the finite-adelic subgroup and by the determinant-one row isometries at each infinite place and under right convolution by factorizable archimedean-bi-finite test functions, minimal among such subspaces. Let $x$ lie in $V$, be right invariant under $\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, and lie in the archimedean type cut $\bigsqcap_w\bigvee_i$ of the submodules attached to `tys`. Let $w_0\in\mathbb{R}$ satisfy $\|\xi(z)\|=\|z\|_{\mathbb{A}}^{w_0}$ for all ideles $z$, and let $g$ have trivial archimedean component. Then there are $\delta>0$ and $C\in\mathbb{R}$ such that for every $k$ with trivial finite component whose archimedean component at each infinite place $w$ is a row isometry (unit determinant norm and preservation of $\|x\|^2+\|y\|^2$ under the row action), and every idele $a$ with finite part $1$, the first Whittaker coefficient $\int x(u(t)\,\mathrm{diag}(a,1)kg)\,\psi_K(-t)\,d\nu(t)$, taken with respect to the standard additive character of $K$ and the conditioned Haar measure $\nu$, has norm at most $C\prod_{w\mid\infty}\bigl(\|a_w\|^{\,\mathrm{mult}(w)w_0/2}\min(1,\|a_w\|)^{\delta}\bigr)$.
--
--   This is the archimedean decay estimate for Whittaker functions of a vector in a cuspidal constituent of $\mathrm{GL}_2$ over a number field, in the form of a power bound at the origin of the diagonal torus, joint over the infinite places and uniform over the maximal compact at infinity, evaluated at a fixed finite translate $g$. It feeds the growth bounds for class sums and the analytic continuation and non-vanishing of Rankin–Selberg integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_norm_whittakerCoefficient_diagOne_mul_le_ideleNorm_rpow_mul_prod_min_of_isCuspConstituent_mul_of_glArch_eq_one.lean

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

theorem AutomorphicForm.CuspidalConstituent.exists_norm_whittakerCoefficient_diagOne_mul_le_ideleNorm_rpow_mul_prod_min_of_isCuspConstituent_mul_of_glArch_eq_one
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
