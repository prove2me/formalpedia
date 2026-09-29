-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_of_isCuspConstituent
-- name    : AutomorphicForm.CuspidalConstituent.exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_of_isCuspConstituent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/c9a302df-95d2-5e4c-be06-1c11a4c91e80
-- title:
--   Uniform bound for archimedean translates of Whittaker coefficients
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $c>0$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Put $D=\bigcup_{t\in T}\{g t : g\in \Sigma\}$, where $\Sigma$ is the centre-cut Siegel set of parameters $c,u,d_1,d_2$ (the $g$ whose finite part is integral, whose archimedean local heights are all $\ge c$, whose archimedean $x$-windows satisfy $\mathrm{xWindowSq}\le u^2$, and whose archimedean determinant norms all lie in $[d_1,d_2]$), and assume $D$ covers modulo the centre: every $g$ admits $\gamma\in\mathrm{GL}_2(K)$ and an idèle unit $z$ with $\gamma g\,z\cdot 1\in D$. Consider the carrier data `productionPinsOf` attached to $D$, to the levels $U(N)=\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, to the Hecke generators $\mathrm{heckeGen}$ at the finite places, and to the adelic box (so the centre subgroup is all of $(\mathbb{A}_K)^\times$, the group measure is the adelic Haar measure on $\mathrm{GL}_2$, and the additive measure is Haar conditioned on the box). Let $\xi\colon(\mathbb{A}_K)^\times\to\mathbb{C}^\times$ be a character, $N\ne 0$ an ideal of $\mathcal{O}_K$, $\mathrm{tys}$ an archimedean type family, and $V$ a submodule of $\mathbb{C}$-valued functions on $\mathrm{GL}_2(\mathbb{A}_K)$ which is a cuspidal constituent for these data and $\xi$: $V$ is a cusp subrepresentation (contained in the $K$-finite cusp submodule, stable under right translation by the finite-adelic subgroup and by the row-isometry subgroups at each infinite place, and stable under right convolution by factorizable archimedean-bifinite test functions), $V\ne 0$, and every cusp subrepresentation contained in $V$ is $0$ or $V$. Let $x$ lie in $V$, be invariant under right multiplication by $U(N)$, and lie in the archimedean cut submodule of $\mathrm{tys}$, and let $w_0\in\mathbb{R}$ satisfy $\|\xi(z)\|=\|z\|^{w_0}$ for all idèle units $z$, where $\|\cdot\|$ is the idèle norm given by the Haar character. Then there are an $m\in\mathbb{N}$, functions $y_1,\dots,y_m$ each again in $V$, $U(N)$-invariant and in the archimedean cut submodule of $\mathrm{tys}$, and a real $M$, such that for every $k\in\mathrm{GL}_2(\mathbb{A}_K)$ whose finite component is trivial and whose archimedean component at each infinite place $w$ is a row isometry (its determinant has norm $1$ and right multiplication by it preserves $\|x\|^2+\|y\|^2$ on row vectors), there exist scalars $c_1,\dots,c_m\in\mathbb{C}$ and an idèle unit $\varepsilon$ with trivial finite component and idèle norm $1$, with $\|c_i\|\le M$ for all $i$, such that for all $g\in\mathrm{GL}_2(\mathbb{A}_K)$ the Whittaker coefficient at $\alpha=1$ for the standard additive character satisfies $W(x)(gk)=\sum_{i=1}^m c_i\,W(y_i)\big(g\,\mathrm{diag}(\varepsilon,1)\big)$, where $W(\varphi)(h)=\int \varphi(u(t)h)\,\psi_K(-t)\,d\nu(t)$ with $u(t)$ the upper unipotent matrix and $\nu$ the box-conditioned additive Haar measure.
--
--   This is the archimedean uniformity statement for Whittaker functions of a cuspidal constituent: translating a level- and type-cut vector by an element of the archimedean maximal compact subgroup replaces its first Whittaker coefficient by a combination, with coefficients bounded independently of the translate, of the Whittaker coefficients of finitely many vectors of the same kind evaluated at a norm-one diagonal twist. It feeds the Rankin–Selberg estimates [`AutomorphicForm.RankinSelberg.exists_testData_sPartIntegral_pair_analyticOnNhd_ne_zero`](thm.html#AutomorphicForm.RankinSelberg.exists_testData_sPartIntegral_pair_analyticOnNhd_ne_zero) and [`AutomorphicForm.RankinSelberg.exists_testData_sPartIntegral_self_analyticOnNhd_re_pos`](thm.html#AutomorphicForm.RankinSelberg.exists_testData_sPartIntegral_self_analyticOnNhd_re_pos), where uniform control over the compact group is needed to integrate the $s$-part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_of_isCuspConstituent.lean

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

theorem AutomorphicForm.CuspidalConstituent.exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_of_isCuspConstituent
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
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀) :
    ∃ (m : ℕ) (ys : Fin m → (AdelicGL2 (𝓞 K) K → ℂ)) (M : ℝ),
      (∀ i, ys i ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys) ∧
      ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
        ∃ (cs : Fin m → ℂ) (ε : (AdeleRing (𝓞 K) K)ˣ),
          ((ε : AdeleRing (𝓞 K) K)).2 = 1 ∧ NumberField.TateGlobal.ideleNorm K ε = 1 ∧
          (∀ i, ‖cs i‖ ≤ M) ∧
          ∀ g : AdelicGL2 (𝓞 K) K,
            whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
              (g * k) =
              ∑ i, cs i * whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (ys i) 1
              (g * diagOne ε) := by sorry
