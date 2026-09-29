-- Prove2me | Theorems.Thm_AutomorphicForm_exists_fractionalIdeal_forall_whittakerCoefficient_eq_zero_of_not_mem_of_forall_mul_idealBall_eq
-- name    : AutomorphicForm.exists_fractionalIdeal_forall_whittakerCoefficient_eq_zero_of_not_mem_of_forall_mul_idealBall_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/89ab2c83-cfca-5a4d-a913-01b61ad2c71d
-- title:
--   Whittaker coefficients on a window vanish outside one fractional ideal
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers, let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$ (the group `AdelicGL2 (𝓞 K) K`), and let $N$ be a non-zero ideal of $\mathcal{O}_K$. The assertion is that there is a unit $I$ of the group of invertible fractional ideals of $K$ with the following property, for every function $f\colon \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ at once. Suppose $f$ satisfies $f(h u')=f(h)$ for all $h$ and all $u'$ in `finiteAdelicGL2Subgroup K`, the kernel of the archimedean component map $\mathrm{glArch}$, such that every entry of $\mathrm{glFin}(u')-1$ and every entry of $(\mathrm{glFin}(u'))^{-1}-1$ lies in `idealBall (𝓞 K) K N`, i.e. has valuation at most the bound `idealBound` attached to $N$ at each finite place. Then for every $g$ in $\bigcup_{x\in T}\{\,s x : s \in$ `centreCutSiegelSet K c u d₁ d₂`$\,\}$ — the set of $s$ whose finite part is integral and whose archimedean component at each infinite place $w$ has $c\le \lVert\det\rVert/\mathrm{rowNormSq}$, $\mathrm{topNormSq}/\mathrm{rowNormSq}-(\lVert\det\rVert/\mathrm{rowNormSq})^2\le u^2$ and $\mathrm{archDetNorm}_w(s)\in[d_1,d_2]$ — and every $\alpha\in K$ with $\alpha\notin I$, the Whittaker coefficient $$\int f(\mathrm{unipotentGL2}(x)\,g)\,\psi\bigl(-\alpha x\bigr)\,d\nu(x)=0,$$ where $\psi$ is [`NumberField.StandardAddChar.stdAddChar K`](def/NumberField_AdelicTraceFin.html#L198) and $\nu$ is the additive adelic Haar measure conditioned on `adelicBox K` (the product of the infinite box with the integral finite adeles), this being the measure datum of the carrier pins `productionPinsOf` built from the above window, from the groups $N'\mapsto$ `levelOne` $\sqcap$ `finiteAdelicGL2Subgroup`, from the Hecke generators `heckeGen`, and from `adelicBox K`. The point is the uniformity: $I$ depends only on $K$, on $c,u,d_1,d_2,T$ and on $N$, not on $f$, $g$ or $\alpha$.
--
--   This is the support statement for the adelic Fourier–Whittaker expansion of a right congruence-invariant function on $\mathrm{GL}_2(\mathbb{A}_K)$ restricted to a finite union of translates of a centre-cut Siegel window: only characters $\alpha$ lying in a single fractional ideal, determined by the window and the congruence ideal alone, can contribute. It feeds the decay estimate [`AutomorphicForm.exists_forall_norm_le_mul_prod_rpow_neg_of_hasDerivAt_chains_of_constantTerm_eq_zero_of_mem_idealBall`](thm.html#AutomorphicForm.exists_forall_norm_le_mul_prod_rpow_neg_of_hasDerivAt_chains_of_constantTerm_eq_zero_of_mem_idealBall), where a uniform bound on the set of contributing $\alpha$ is needed to sum the Whittaker terms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_fractionalIdeal_forall_whittakerCoefficient_eq_zero_of_not_mem_of_forall_mul_idealBall_eq.lean

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
open scoped nonZeroDivisors

theorem
AutomorphicForm.exists_fractionalIdeal_forall_whittakerCoefficient_eq_zero_of_not_mem_of_forall_mul_idealBall_eq
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (N : Ideal (𝓞 K))
    (hN : N ≠ ⊥) :
    ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      ∀ (f : AdelicGL2 (𝓞 K) K → ℂ),
        (∀ (h : AdelicGL2 (𝓞 K) K), ∀ u' ∈ finiteAdelicGL2Subgroup K,
          (∀ i j, ((glFin (𝓞 K) K u' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) i j ∈
            idealBall (𝓞 K) K N) →
          (∀ i j, ((((glFin (𝓞 K) K u')⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) - 1) i j ∈ idealBall (𝓞 K) K N) →
          f (h * u') = f h) →
        ∀ g ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
          ∀ α : K, α ∉ (I : FractionalIdeal (𝓞 K)⁰ K) →
            whittakerCoefficient K
              (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
                (fun N' : Ideal (𝓞 K) => levelOne (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K)
                (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
              (NumberField.StandardAddChar.stdAddChar K) f α g = 0 := by sorry
