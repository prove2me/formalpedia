-- Prove2me | Theorems.Thm_AutomorphicForm_twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_one
-- name    : AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/b428ab28-6c25-5d6b-9517-df5785a433a3
-- title:
--   Weighted Hecke-word fundamental lemma at a split place
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an extension of $K$ whose degree $\ell = \operatorname{finrank}_K L$ is prime, let $\sigma$ be a $K$-automorphism of $L$ with $\sigma \neq 1$, and let $v$ be a height-one prime of $\mathcal{O}_K$ such that every height-one prime $w$ of $\mathcal{O}_L$ with $w \cap \mathcal{O}_K = v$ has ramification index $1$ over $v$. Fix, for each height-one prime $u$ of $\mathcal{O}_K$, a prime $ws\,u$ of $\mathcal{O}_L$ above $u$, and assume the inertia degree of $v$ in $w := ws\,v$ is $1$. On the $L$-side, let $\varpi$ be an irreducible element of the valuation ring of $L_w$ whose image in $L_w$ is nonzero, let $rL : \mathrm{Fin}\,n \to \mathrm{GL}_2(L_w)$ satisfy [`HeckeIntegralSeam.IsHeckeCosetSystem`](def/LocalLanglands_HeckeCosetSystem.html#L15) for the subgroup $U_w$ of $\mathrm{GL}_2(L_w)$ that is the image of $\mathrm{GL}_2$ of the valuation ring and the element $\mathrm{diag}(\varpi,1)$ — that is, each $rL\,i$ lies in the double coset $U_w\,\mathrm{diag}(\varpi,1)\,U_w$, the $rL\,i$ meet every left $U_w$-coset in that double coset, and distinct indices give distinct cosets in $\mathrm{GL}_2(L_w)/U_w$ — and let $z$ be the scalar matrix $\varpi \cdot 1$. Let $\varpi_K$, $rK : \mathrm{Fin}\,n_K \to \mathrm{GL}_2(K_v)$ and $z_K$ be data of exactly the same shape at $v$ over $K$, and let $k, j$ be natural numbers. Let $a \neq b$ be units of $K_v$, and $\alpha, \beta$ units of $L \otimes_K K_v$, such that the norm string of $\mathrm{diag}(\alpha,\beta)$ — the product of the iterates $(\sigma_{\mathrm{GL}})^{i}\mathrm{diag}(\alpha,\beta)$ for $i = 0,\dots,\ell-1$, where $\sigma_{\mathrm{GL}}$ is $\sigma \otimes 1$ acting entrywise — equals the image of $\mathrm{diag}(a,b)$ under $\mathrm{GL}_2(K_v) \to \mathrm{GL}_2(L \otimes_K K_v)$ induced by $x \mapsto 1 \otimes x$. Let $\tau$ be a Haar measure, for the Borel structure, on the centralizer of $\mathrm{diag}(a,b)$ in $\mathrm{GL}_2(K_v)$ giving mass $1$ to the elements lying in [`AutomorphicForm.localIntegralSet`](def/AutomorphicForm_LocalOrbitalBase.html#L100), the set of $g$ with $g$ and $g^{-1}$ integral at $v$; let $\tau'$ be a Haar measure on the twisted centralizer $\{t : t\,\delta\,(\sigma_{\mathrm{GL}}t)^{-1} = \delta\}$ of $\delta = \mathrm{diag}(\alpha,\beta)$ giving mass $1$ to the elements lying in [`AutomorphicForm.semiLocalIntegralSet`](def/AutomorphicForm_TwistedOrbital.html#L136), the set of $g$ in $\mathrm{GL}_2(L \otimes_K K_v)$ with $g$ and $g^{-1}$ in the image of the semi-local integers. Finally let $J, J' \in \mathbb{C}$ be such that $J$ is a weighted orbital integral of $\mathrm{diag}(a,b)$ against $\tau$ and the normalised local Haar measure, with the weight `LocalWeight.weight`, of the Satake combination $x \mapsto \sum_{e} \mathrm{slotCoeff}(e)\sum_{\iota : \mathrm{Fin}(e\,0) \to \mathrm{Fin}\,n_K}\mathbf{1}_{\mathrm{localIntegralSet}}\big((\prod_m rK(\iota\,m)\cdot z_K^{\,e\,1})^{-1}x\big)$, the sum being over the support of `SatakeCombination.slotWord`, namely $\mathrm{univWord}$ of degree parameter (inertia degree $-1$) in $k$ and $j$, with $\mathrm{slotCoeff}(e)$ its coefficient at $e$ times $N(v)^{e\,1}/N(w)^{j}$; and $J'$ is a twisted weighted orbital integral of $\delta$ against $\tau'$ and the semi-local Haar measure, with weight the sum of local weights over the places above $v$, of $x \mapsto \sum_{\iota : \mathrm{Fin}\,k \to \mathrm{Fin}\,n}\mathbf{1}_{\mathrm{semiLocalIntegralSet}}\big(\mathrm{semiLocalComponent}(\mathrm{localEmbed}(\prod_m rL(\iota\,m)\cdot z^{j}))^{-1}x\big)$. Then $J' = \ell\,J$.
--
--   This is the completely split case of the weighted fundamental lemma comparing the twisted weighted orbital integral of a spherical Hecke word $T_w^k z_w^j$ on $\mathrm{GL}_2$ over $L$ with the weighted orbital integral of its base-change Satake combination over $K$, at a regular diagonal norm pair with tori normalised to mass one. It is the input to the unramified case, [`AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_unramified`](thm.html#AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_unramified), in the comparison of hyperbolic terms in the twisted and untwisted trace formulae for a cyclic extension of prime degree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_one.lean

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

theorem AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)

    (ws : ∀ u : HeightOneSpectrum (𝓞 K), u.Extension (𝓞 L))
    (hsplit : v.asIdeal.inertiaDeg' (ws v).1.asIdeal = 1)
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
