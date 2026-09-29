-- Prove2me | Theorems.Thm_AutomorphicForm_exists_diagUnits2_normString_isOrbitalIntegral_ne_zero_isTwistedOrbitalIntegral_eq_heckeWord_of_ramificationIdx_eq_one_of_prime
-- name    : AutomorphicForm.exists_diagUnits2_normString_isOrbitalIntegral_ne_zero_isTwistedOrbitalIntegral_eq_heckeWord_of_ramificationIdx_eq_one_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/da5eee15-e95b-503c-927e-da335601d2b1
-- title:
--   Matched split pair with equal non-zero twisted orbital integral
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an extension of $K$ whose degree $[L:K]$ is prime, let $\sigma$ be a non-trivial $K$-automorphism of $L$, let $v$ be a height-one prime of $\mathcal{O}_K$ such that every height-one prime of $\mathcal{O}_L$ lying under $v$ has ramification index $1$ over it, and let $w$ be a prime of $\mathcal{O}_L$ above $v$. Fix an irreducible element $\varpi$ of the valuation ring of $L_w$ with non-zero image in $L_w$, a family $rT : \mathrm{Fin}\,n \to \mathrm{GL}_2(L_w)$ forming a Hecke coset system for the double coset of $\mathrm{diag}(\varpi,1)$ modulo the subgroup $\mathrm{GL}_2(\mathcal{O}_{L_w})$ (each $rT(i)$ lies in the double coset, the cosets $rT(i)\,\mathrm{GL}_2(\mathcal{O}_{L_w})$ cover it and are pairwise distinct), and $z \in \mathrm{GL}_2(L_w)$ with underlying matrix $\varpi\cdot 1$; fix the same data $\varpi_K, rK : \mathrm{Fin}\,n_K \to \mathrm{GL}_2(K_v), z_K$ at $v$; and fix $k, j \in \mathbb{N}$. Then there exist units $a,b$ of $K_v$, units $\alpha,\beta$ of $L \otimes_K K_v$, measures $\tau$ on the centraliser of $\mathrm{diag}(a,b)$ in $\mathrm{GL}_2(K_v)$ and $\tau'$ on the $\sigma$-twisted centraliser $\{t \mid t\,\delta\,\sigma(t)^{-1} = \delta\}$ of $\delta = \mathrm{diag}(\alpha,\beta)$ in $\mathrm{GL}_2(L \otimes_K K_v)$ (both carrying their Borel structures), and complex numbers $I, I'$, such that: $a \neq b$; the norm string $\prod_{i<[L:K]} \sigma^{i}(\delta)$ equals the image of $\mathrm{diag}(a,b)$ under $x \mapsto 1 \otimes x$; $\tau$ is a Haar measure giving mass $1$ to the elements of the centraliser whose matrix and inverse matrix have entries in $\mathcal{O}_{K_v}$, and $\tau'$ is a Haar measure giving mass $1$ to the elements of the twisted centraliser whose matrix and inverse matrix have entries in the image of the integers of $L\otimes_K K_v$; $I$ is an orbital integral at $\mathrm{diag}(a,b)$ with respect to $\tau$, i.e. $I = \int f(x^{-1}\mathrm{diag}(a,b)x)\,\omega(x)$ against the local Haar measure for some non-negative compactly supported measurable weight $\omega$ normalising the centraliser integrals to $1$, of the function $$f(x) = \sum_{r} c_r\, N(v)^{r(1)} N(w)^{-j} \sum_{\iota : \mathrm{Fin}\,r(0) \to \mathrm{Fin}\,n_K} \mathbf{1}\big(\big(\textstyle\prod_m rK(\iota(m))\cdot z_K^{\,r(1)}\big)^{-1}x\big),$$ where $r$ runs over the support and $c_r$ over the coefficients of the polynomial $\mathrm{satakePow}(f_{w/v})(X_0,X_1)^k\,(X_1^{f_{w/v}})^j$ with $f_{w/v}$ the inertia degree of $w$ over $v$, and $\mathbf{1}$ the indicator of the integral set; $I'$ is a twisted orbital integral at $\delta$ with respect to $\tau'$, i.e. $I' = \int \varphi(x^{-1}\delta\,\sigma(x))\,\omega'(x)$ against the semi-local Haar measure, of $\varphi(x) = \sum_{\iota : \mathrm{Fin}\,k \to \mathrm{Fin}\,n} \mathbf{1}\big(\big(\prod_m rT(\iota(m))\cdot z^{\,j}\big)^{-1}x\big)$, the word at $w$ being transported to $\mathrm{GL}_2(L\otimes_K K_v)$ through the local embedding into the finite adeles of $L$ followed by the semi-local component map; and finally $I \neq 0$ and $I' = I$.
--
--   This is the fundamental-lemma comparison for a single Hecke word at an unramified finite place, in the form of an existence statement producing a regular split element $\mathrm{diag}(a,b)$ which is a twisted norm of $\mathrm{diag}(\alpha,\beta)$, together with normalised Haar measures on the ordinary and twisted centralisers for which the twisted orbital integral of the base-change Hecke word at $w$ coincides with the orbital integral of the corresponding Satake combination of Hecke words at $v$, the common value being non-zero. It serves as the anchoring place in the comparison of hyperbolic terms, and is used in the assembly of the winding identity for the base-change trace formula.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_diagUnits2_normString_isOrbitalIntegral_ne_zero_isTwistedOrbitalIntegral_eq_heckeWord_of_ramificationIdx_eq_one_of_prime.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_diagUnits2_normString_isOrbitalIntegral_ne_zero_isTwistedOrbitalIntegral_eq_heckeWord_of_ramificationIdx_eq_one_of_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime)
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w' : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w' = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w').asIdeal w'.asIdeal = 1)
    (w : v.Extension (𝓞 L))
    (ϖ : w.1.adicCompletionIntegers L) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ ≠ 0)
    (n : ℕ) (rT : Fin n → GL (Fin 2) (w.1.adicCompletion L))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))
      (LocalGL2.diagPi ϖ hϖ0) rT)
    (z : GL (Fin 2) (w.1.adicCompletion L))
    (hz : (z : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ •
        (1 : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)))
    (ϖK : v.adicCompletionIntegers K) (hϖK : Irreducible ϖK)
    (hϖK0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK ≠ 0)
    (nK : ℕ) (rK : Fin nK → GL (Fin 2) (v.adicCompletion K))
    (hrK : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
      (LocalGL2.diagPi ϖK hϖK0) rK)
    (zK : GL (Fin 2) (v.adicCompletion K))
    (hzK : (zK : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (k j : ℕ) :
    ∃ (a b : (v.adicCompletion K)ˣ) (α β : (L ⊗[K] v.adicCompletion K)ˣ)
      (τ : @Measure (localCentralizer K v (diagUnits2 a b)) (localCentralizerBorel K v (diagUnits2 a b)))
      (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
        (twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)))
      (I I' : ℂ),
      a ≠ b ∧
      normString K L (v.adicCompletion K) σ (diagUnits2 α β) = toTensorGL K L (v.adicCompletion K) (diagUnits2 a b) ∧
      @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v (diagUnits2 a b)) τ ∧
      τ {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ localIntegralSet K v} = 1 ∧
      @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ' ∧
      τ' {t | (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ semiLocalIntegralSet K L v} = 1 ∧
      IsOrbitalIntegral K v (diagUnits2 a b) τ
        (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ r ∈ (SatakeCombination.univWord (v.asIdeal.inertiaDeg' w.1.asIdeal - 1) k j).support,
          (SatakeCombination.univWord (v.asIdeal.inertiaDeg' w.1.asIdeal - 1) k j).coeff r *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (r 1) / (Ideal.absNorm w.1.asIdeal : ℂ) ^ j *
            ∑ ι : Fin (r 0) → Fin nK,
              (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rK (ι m)).prod * zK ^ (r 1))⁻¹ * x)) I ∧
      IsTwistedOrbitalIntegral K L v σ (diagUnits2 α β) τ'
        (fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
        ∑ ι : Fin k → Fin n,
          (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
            ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w.1
              ((List.ofFn fun m => rT (ι m)).prod * z ^ j)))⁻¹ * x)) I' ∧
      I ≠ 0 ∧ I' = I := by sorry
