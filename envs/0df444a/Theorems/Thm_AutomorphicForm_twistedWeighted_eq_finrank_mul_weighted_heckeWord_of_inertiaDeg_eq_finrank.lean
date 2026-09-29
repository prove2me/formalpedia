-- Prove2me | Theorems.Thm_AutomorphicForm_twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_finrank
-- name    : AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/76adcd0c-8e82-5837-b41f-f45e9e5b207e
-- title:
--   Weighted fundamental lemma for Hecke words at an inert place
-- statement:
--   Let $L/K$ be an extension of number fields of prime degree $\ell = [L:K]$, let $\sigma$ be a non-identity $K$-algebra automorphism of $L$, and let $v$ be a height-one prime of $\mathcal{O}_K$ such that every prime of $\mathcal{O}_L$ lying under $v$ has ramification index $1$ over it. A choice function `ws` picks for each height-one prime $u$ of $\mathcal{O}_K$ a prime of $\mathcal{O}_L$ over $u$, and the chosen prime $w$ over $v$ is assumed to have inertia degree $\ell$ over $v$. Fix an irreducible $\varpi$ in the ring of integers of $L_w$ with non-zero image in $L_w$, a family $r_L : \mathrm{Fin}\,n \to \mathrm{GL}_2(L_w)$ which is a Hecke coset system for the double coset of $\mathrm{diag}(\varpi,1)$ with respect to the image of $\mathrm{GL}_2(\mathcal{O}_w)$ — each $r_L(i)$ lies in the double coset, every element of the double coset is left-congruent to some $r_L(i)$ modulo the subgroup, and $i \mapsto r_L(i)$ induces an injection into the coset space — and $z$ the scalar matrix $\varpi \cdot 1$; fix data $\varpi_K$, $r_K : \mathrm{Fin}\,n_K \to \mathrm{GL}_2(K_v)$, $z_K$ of the same shape at $v$ over $K$, and natural numbers $k, j$. Let $a \ne b$ be units of $K_v$ and $\alpha, \beta$ units of $L \otimes_K K_v$ such that the twisted norm string $\prod_{i<\ell} (\sigma\text{-twist})^i$ of $\mathrm{diag}(\alpha,\beta)$ equals the image of $\mathrm{diag}(a,b)$ under $\mathrm{GL}_2(K_v) \to \mathrm{GL}_2(L \otimes_K K_v)$. Let $\tau$ be a Haar measure on the centraliser of $\gamma = \mathrm{diag}(a,b)$ in $\mathrm{GL}_2(K_v)$ giving mass $1$ to the set of elements with integral entries whose inverse also has integral entries, and $\tau'$ a Haar measure on the $\sigma$-twisted centraliser $\{t : t\delta\sigma(t)^{-1} = \delta\}$ of $\delta = \mathrm{diag}(\alpha,\beta)$ giving mass $1$ to the corresponding semi-local integral set. Finally let $J, J' \in \mathbb{C}$ be such that: $J$ is a weighted orbital integral $\int f(x^{-1}\gamma x)\,\mathrm{weight}(x)\,s(x)$ against the normalised local Haar measure on $\mathrm{GL}_2(K_v)$, for a section function matched with $\tau$, where $f$ is the base-change combination $\sum_e \mathrm{slotCoeff}(e)\sum_\iota \mathbf{1}_{\text{integral}}\big((\prod_m r_K(\iota m)\, z_K^{e_1})^{-1}x\big)$, the sum being over the support of the Satake word $\mathrm{satakePow}_{\ell}(X_0,X_1)^k (X_1^{\ell})^j$ with coefficients twisted by $|v|^{e_1}/|w|^{j}$; and $J'$ is a twisted weighted orbital integral $\int \varphi(x^{-1}\delta\,\sigma(x))\,\mathrm{weight}_{\text{semi-loc}}(x)\,s(x)$ against the semi-local Haar measure on $\mathrm{GL}_2(L \otimes_K K_v)$, for a twisted section function matched with $\tau'$, where $\varphi(x) = \sum_{\iota : \mathrm{Fin}\,k \to \mathrm{Fin}\,n} \mathbf{1}_{\text{semi-local integral}}\big(c((\prod_m r_L(\iota m))\,z^{j})^{-1}x\big)$, with $c$ the embedding of $\mathrm{GL}_2(L_w)$ into $\mathrm{GL}_2$ of the finite adeles of $L$ followed by the semi-local component map at $v$. The conclusion is $J' = \ell \cdot J$.
--
--   This is the weighted (non-invariant) form of the base-change fundamental lemma for spherical Hecke words on $\mathrm{GL}_2$, in the inert case where the chosen prime above $v$ has residue degree $[L:K]$ so that $L \otimes_K K_v = L_w$, as in Langlands' treatment of base change for $\mathrm{GL}(2)$. It is the inert branch used by [`AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_unramified`](thm.html#AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_unramified), which assembles the split and inert cases at an unramified place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_finrank.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_finrank
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)

    (ws : ∀ u : HeightOneSpectrum (𝓞 K), u.Extension (𝓞 L))
    (hinert : v.asIdeal.inertiaDeg' (ws v).1.asIdeal = Module.finrank K L)
    (ϖ : (ws v).1.adicCompletionIntegers L) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) ϖ ≠ 0)
    (n : ℕ) (rL : Fin n → GL (Fin 2) ((ws v).1.adicCompletion L))
    (hrL : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
      (LocalGL2.diagPi ϖ hϖ0) rL)
    (z : GL (Fin 2) ((ws v).1.adicCompletion L))
    (hz : (z : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
      algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) ϖ •
        (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)))

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
    (k j : ℕ)

    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b)
    (α β : (L ⊗[K] v.adicCompletion K)ˣ)
    (hN : AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a b))
    (τ : @Measure (AutomorphicForm.localCentralizer K v (diagUnits2 a b))
      (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)) τ)
    (hτ1 : τ {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} = 1)
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)))
    (hτ' : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ')
    (hτ'1 : τ' {t | (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈
      AutomorphicForm.semiLocalIntegralSet K L v} = 1)
    (J J' : ℂ)
    (hJ : AutomorphicForm.IsWeightedOrbitalIntegral K v (diagUnits2 a b) τ
      (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ e ∈ (SatakeCombination.slotWord K L ws v k j).support,
          SatakeCombination.slotCoeff K L ws v k j e *
            ∑ ι : Fin (e 0) → Fin nK,
              (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rK (ι m)).prod * zK ^ (e 1))⁻¹ * x))
      J)
    (hJ' : AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ'
      (fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
        ∑ ι : Fin k → Fin n,
          (AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
            ((AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
              ((List.ofFn fun m => rL (ι m)).prod * z ^ j)))⁻¹ * x))
      J') :
    J' = (Module.finrank K L : ℂ) * J := by sorry
