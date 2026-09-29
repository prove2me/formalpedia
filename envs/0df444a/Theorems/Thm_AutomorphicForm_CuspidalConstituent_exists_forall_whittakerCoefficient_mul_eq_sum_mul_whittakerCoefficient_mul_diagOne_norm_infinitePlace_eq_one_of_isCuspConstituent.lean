-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_norm_infinitePlace_eq_one_of_isCuspConstituent
-- name    : AutomorphicForm.CuspidalConstituent.exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_norm_infinitePlace_eq_one_of_isCuspConstituent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/a80949b0-1fae-5c97-b8eb-bab6c4a83078
-- title:
--   Whittaker coefficients of a cut vector, uniformly over K_∞
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $c>0$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$ such that the set $D=\bigcup_{t\in T} (\,\cdot\,t)\,[\,\text{centreCutSiegelSet}\;K\,c\,u\,d_1\,d_2\,]$ covers modulo the centre: every $g$ can be written with $\gamma\in\mathrm{GL}_2(K)$ and a scalar idele $z$ so that $\gamma g z\in D$. Consider the carrier data `productionPinsOf` attached to $D$, to the level groups $N\mapsto \mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, to the local Hecke elements $\mathrm{heckeGen}$ and to the adelic box, whose central subgroup is all of $\mathbb{A}_K^\times$; let $\xi:\mathbb{A}_K^\times\to\mathbb{C}^\times$ be a character with $|\xi(z)|=\|z\|^{w_0}$ for some real $w_0$, where $\|\cdot\|$ is the idele norm given by the Haar modulus. Let $N\neq 0$ be an ideal of $\mathcal{O}_K$, let $\mathrm{tys}$ be a family of archimedean types, let $V$ be a cuspidal constituent for these data and $\xi$ (a cuspidal subrepresentation that is nonzero and minimal among cuspidal subrepresentations contained in it), and let $x$ lie in $V$, be right invariant under $\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, and lie in the archimedean type-cut submodule of $\mathrm{tys}$. Then there are $m\in\mathbb{N}$, functions $y_1,\dots,y_m$ in that same intersection of $V$ with the level-invariant and type-cut submodules, and a real $M$, such that for every $k\in\mathrm{GL}_2(\mathbb{A}_K)$ whose finite component is $1$ and whose component at each infinite place $w$ is a row isometry (determinant of absolute value one and preserving the sum of squared absolute values of the two rows' pairings with any vector), there are scalars $c_1,\dots,c_m\in\mathbb{C}$ with $|c_i|\le M$ and an idele unit $\varepsilon$ with trivial finite component, $|\varepsilon_w|=1$ at every infinite place and idele norm $1$, such that for all $g$ the first Whittaker coefficient, taken with respect to the standard additive character and the additive Haar measure conditioned on the adelic box, satisfies $W_1(x)(gk)=\sum_{i=1}^m c_i\,W_1(y_i)\!\left(g\,\mathrm{diag}(\varepsilon,1)\right)$. The vectors $y_i$ and the bound $M$ are chosen uniformly in $k$, while the $c_i$ and $\varepsilon$ depend on $k$.
--
--   This is the uniformity statement that replaces a right translate by an arbitrary element of the archimedean maximal compact subgroup by a torus twist $\mathrm{diag}(\varepsilon,1)$ with $\varepsilon$ of absolute value one at each infinite place, at the cost of a finite, boundedly weighted sum of Whittaker coefficients of vectors of the same level and archimedean type. It feeds the two bounds for Whittaker coefficients on the torus at real and at complex places, stated for cuspidal constituents with trivial archimedean part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_norm_infinitePlace_eq_one_of_isCuspConstituent.lean

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

theorem AutomorphicForm.CuspidalConstituent.exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_norm_infinitePlace_eq_one_of_isCuspConstituent
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
          ((ε : AdeleRing (𝓞 K) K)).2 = 1 ∧ (∀ w : InfinitePlace K, ‖((ε : AdeleRing (𝓞 K) K)).1 w‖ = 1) ∧
          NumberField.TateGlobal.ideleNorm K ε = 1 ∧
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
