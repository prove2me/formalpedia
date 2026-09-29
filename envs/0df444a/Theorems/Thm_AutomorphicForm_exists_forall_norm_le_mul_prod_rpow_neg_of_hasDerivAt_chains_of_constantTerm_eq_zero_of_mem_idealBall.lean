-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_norm_le_mul_prod_rpow_neg_of_hasDerivAt_chains_of_constantTerm_eq_zero_of_mem_idealBall
-- name    : AutomorphicForm.exists_forall_norm_le_mul_prod_rpow_neg_of_hasDerivAt_chains_of_constantTerm_eq_zero_of_mem_idealBall
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/a234fcb6-7e98-5816-b74c-131c3ff3a5bd
-- title:
--   Decay bound for cuspidal functions on a centre-cut Siegel window
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2\in\mathbb{R}$, let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$, let $N\neq 0$ be an ideal of $\mathcal{O}_K$, let $s_0>0$ and let $M''\in\mathbb{N}$. Then there are $M\in\mathbb{N}$ and $C>0$ with the following property. Let $f:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous, invariant under left translation by the image of $\mathrm{GL}_2(K)$ under `globalPoints`, and invariant under right translation by every $u'$ in the kernel of the archimedean projection `glArch` such that all entries of $\mathrm{glFin}\, u'-1$ and of $(\mathrm{glFin}\, u')^{-1}-1$ lie in $\mathrm{idealBall}\, N=\{x:\ \mathrm{v}(x_v)\le \mathrm{idealBound}\, N_v\ \forall v\}$. Let $g$ lie in $\bigcup_{x\in T}(\cdot\, x)\big[\mathrm{centreCutSiegelSet}\, K\,c\,u\,d_1\,d_2\big]$, the set of points whose finite part is finite-integral, with $c\le \mathrm{localHeight}$, $\mathrm{xWindowSq}\le u^2$ and $\mathrm{archDetNorm}\in[d_1,d_2]$ at every infinite place, translated on the right by the elements of $T$; assume the constant term $\int f(\mathrm{unipotentGL2}(x)\,g)\,d\nu(x)=0$, where $\nu$ is adelic additive Haar measure conditioned on $\mathrm{adelicBox}\, K$ (the pins produced by `productionPinsOf` with $U:N'\mapsto \mathrm{levelOne}\, N'\sqcap \mathrm{finiteAdelicGL2Subgroup}\, K$ and `heckeGen`). Let $s:\ \mathrm{InfinitePlace}(K)\to\mathbb{R}$ satisfy $s(w)\ge s_0$ for all $w$, and let $\Lambda\in\mathbb{R}$. Suppose that for every $v$ in the mixed space of $K$ there is a sequence $x_\bullet:\mathbb{N}\to(\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C})$ with $x_0=f$, each $x_j$ continuous and invariant under left translation by $\mathrm{unipotentGL2}(\beta)$ for $\beta\in K$, with $t\mapsto x_j(\mathrm{unipotentGL2}((t\cdot v,0))h)$ differentiable at $t=0$ with derivative $x_{j+1}(h)$ for all $j,h$, and such that for all $y$ in the infinite adeles and $t$ in the finite adeles for which all entries of $\mathrm{glFin}(g^{-1}\,\mathrm{unipotentGL2}((0,t))\,g)-1$ and of the corresponding expression for the inverse lie in $\mathrm{idealBall}\, N$, one has $\|x_M(\mathrm{unipotentGL2}((y,t))g)\|\le\Lambda\big(\sum_w \|v\|_w/s(w)\big)^M$. Then $\|f(g)\|\le C\,\Lambda\,\big(\prod_w s(w)^{\mathrm{mult}(w)}\big)^{-M''/[K:\mathbb{Q}]}$.
--
--   This is the quantitative rapid-decay estimate for a function on $\mathrm{GL}_2(\mathbb{A}_K)$ whose constant term along the unipotent radical vanishes: vanishing of the constant term together with bounds on archimedean unipotent derivatives of order $M$ converts into polynomial decay of arbitrary prescribed order $M''$ in the height parameters $s(w)$ on a centre-cut Siegel window. The congruence hypothesis is the principal-type condition cut out by $\mathrm{idealBall}\, N$ on both the matrix and its inverse; the result is used in the cusp-synthesis step of the converse argument, via [`LanglandsTunnell.Converse.CuspSynthesis.memLp_translateSum`](thm.html#LanglandsTunnell.Converse.CuspSynthesis.memLp_translateSum), to obtain integrability of translated sums.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_norm_le_mul_prod_rpow_neg_of_hasDerivAt_chains_of_constantTerm_eq_zero_of_mem_idealBall.lean

import Mathlib
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain

theorem
AutomorphicForm.exists_forall_norm_le_mul_prod_rpow_neg_of_hasDerivAt_chains_of_constantTerm_eq_zero_of_mem_idealBall
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (N : Ideal (𝓞 K))
    (hN : N ≠ ⊥) (s₀ : ℝ) (hs₀ : 0 < s₀) (M'' : ℕ) :
    ∃ (M : ℕ) (C : ℝ), 0 < C ∧
      ∀ (f : AdelicGL2 (𝓞 K) K → ℂ), Continuous f →
        (∀ (γ : GL (Fin 2) K) (h : AdelicGL2 (𝓞 K) K), f (globalPoints (𝓞 K) K γ * h) = f h) →
        (∀ (h : AdelicGL2 (𝓞 K) K), ∀ u' ∈ finiteAdelicGL2Subgroup K,
          (∀ i j, ((glFin (𝓞 K) K u' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) i j ∈
            idealBall (𝓞 K) K N) →
          (∀ i j, ((((glFin (𝓞 K) K u')⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) i j ∈ idealBall (𝓞 K) K N) →
          f (h * u') = f h) →
        ∀ g ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
          @constantTerm _
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
              (fun N' : Ideal (𝓞 K) => levelOne (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K)
              (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
              (fun N' : Ideal (𝓞 K) => levelOne (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K)
              (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
            (fun x => unipotentGL2 x) f g = 0 →
          ∀ (s : InfinitePlace K → ℝ), (∀ w, s₀ ≤ s w) →
          ∀ Λ : ℝ,
            (∀ v : mixedEmbedding.mixedSpace K, ∃ xs : ℕ → AdelicGL2 (𝓞 K) K → ℂ,
              xs 0 = f ∧
              (∀ j, Continuous (xs j)) ∧
              (∀ j (β : K) (h : AdelicGL2 (𝓞 K) K),
                xs j (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * h) = xs j h) ∧
              (∀ j (h : AdelicGL2 (𝓞 K) K),
                HasDerivAt (fun t : ℝ => xs j (unipotentGL2 (R := AdeleRing (𝓞 K) K)
                    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • v), 0) * h)) (xs (j + 1) h) 0) ∧
              (∀ (y : InfiniteAdeleRing K) (t : FiniteAdeleRing (𝓞 K) K),
                (∀ i j, ((glFin (𝓞 K) K (g⁻¹ * unipotentGL2 (R := AdeleRing (𝓞 K) K)
                    (((0, t) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * g) :
                      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) i j ∈ idealBall (𝓞 K) K N) →
                (∀ i j, ((((glFin (𝓞 K) K (g⁻¹ * unipotentGL2 (R := AdeleRing (𝓞 K) K)
                    (((0, t) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * g))⁻¹ :
                      GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
                      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) i j ∈ idealBall (𝓞 K) K N) →
                ‖xs M (unipotentGL2 (R := AdeleRing (𝓞 K) K)
                    (((y, t) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K) * g)‖ ≤
                  Λ * (∑ w : InfinitePlace K, mixedEmbedding.normAtPlace w v / s w) ^ M)) →
            ‖f g‖ ≤ C * Λ * (∏ w : InfinitePlace K, s w ^ w.mult) ^ (-(M'' : ℝ) / Module.finrank ℚ K) := by sorry
