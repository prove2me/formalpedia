-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_norm_archDerivAt_le_of_mem_cut_ofChar_of_forall_isReal
-- name    : AutomorphicForm.CuspidalConstituent.exists_forall_norm_archDerivAt_le_of_mem_cut_ofChar_of_forall_isReal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/db3cf0a4-4652-5060-b88b-8261ff35edcd
-- title:
--   Boundedness of second-order archimedean derivatives on determinant slabs
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real with $c>0$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$ such that $D=\bigcup_{x\in T}\{gx : g\in\Sigma\}$, where $\Sigma$ is the centre-cut Siegel set of parameters $c,u,d_1,d_2$ (finite part integral, local height $\ge c$ at every infinite place, $x$-window square $\le u^2$, and archimedean determinant norm in $[d_1,d_2]$ at every place), covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo the centre: every $g$ admits $\gamma\in\mathrm{GL}_2(K)$ and $z\in\mathbb{A}_K^\times$ with $\gamma g\,z\in D$. Let the carrier data be `productionPinsOf` with domain $D$, level subgroups $N\mapsto \mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, Hecke generators $\mathrm{heckeGen}$, and box $\mathrm{adelicBox}\,K$, so that its central subgroup is all of $\mathbb{A}_K^\times$; let $\xi$ be a character of that group and $V$ a submodule of $\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ that is a cuspidal constituent for $(\text{pins},\xi)$, i.e. a nonzero submodule of the $K$-finite cusp submodule, stable under right translation by the finite-adelic subgroup and by the row-isometry subgroups at the infinite places and under right convolution by factorizable archimedeanly bi-finite test functions, and minimal among such submodules. Assume $|\xi(z)|=\|z\|_{\mathbb{A}}^{w_0}$ for all $z$ and a fixed real $w_0$, and that every infinite place of $K$ is real. Let $N\neq 0$ be an ideal of $\mathcal{O}_K$, let $\chi=(\chi_v)_v$ assign to each infinite place a character of $\mathrm{rowIsometrySubgroup}_0$ of its completion, let $w$ be a real place with $\chi_w=\mathrm{archWeightCharAt}$ of weight $n\in\mathbb{Z}$, and let $y$ lie in $V$, be right invariant under $\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, and lie in the arch cut submodule of the one-dimensional type family attached to $\chi$. Then for all real $0<e_1<e_2$ there is a constant $B$ such that for every $g$ with $\|\det g\|_{\mathbb{A}}\in[e_1,e_2]$ one has $|y(g)|\le B$, $|D_d y(g)|\le B$ for every direction $d\in\{H,E,F\}$, and $|D_dD_{d'}y(g)|\le B$ for all $d,d'$, where $D_d\varphi(g)=\tfrac{d}{dt}\varphi(g\cdot\mathrm{archFlowAt}_w(d,t))|_{t=0}$.
--
--   This is the quantitative regularity input for working with the Casimir element and the raising and lowering operators at a real place: boundedness of a level-and-type cut vector together with its first and second flow derivatives on each slab $e_1\le\|\det g\|_{\mathbb{A}}\le e_2$, which follows from the boundedness of cusp forms on Siegel sets applied to the finitely many shifted cut vectors obtained from $y$. It is used in the proof that the Casimir eigenvalue of such a constituent is real and nonnegative and that the lowering operator is injective on the relevant weight vectors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_forall_norm_archDerivAt_le_of_mem_cut_ofChar_of_forall_isReal.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.exists_forall_norm_archDerivAt_le_of_mem_cut_ofChar_of_forall_isReal
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (hreal : ∀ v : InfinitePlace K, v.IsReal)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (χ : ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ)
    (w : InfinitePlace K) (hw : w.IsReal) (n : ℤ) (hχ : χ w = archWeightCharAt hw n)
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K (ArchTypeFamily.ofChar K χ))
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂) :
    ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖y g‖ ≤ B ∧ (∀ d : ArchDir, ‖archDerivAt hw d y g‖ ≤ B) ∧
        (∀ d d' : ArchDir, ‖archDerivAt hw d (archDerivAt hw d' y) g‖ ≤ B) := by sorry
