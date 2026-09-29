-- Prove2me | Theorems.Thm_AutomorphicForm_eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_relIndex_eq_of_subsingleton_extension
-- name    : AutomorphicForm.eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_relIndex_eq_of_subsingleton_extension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/f8215ec5-0fba-525b-b898-9aa1cd031807
-- title:
--   Twisted weighted orbital integral of the unit at an inert place
-- statement:
--   Let $K \subseteq L$ be number fields with $[L:K]$ prime, let $\sigma$ be a non-identity $K$-automorphism of $L$, and let $v$ be a maximal ideal of $\mathcal{O}_K$, written $q =$ `Ideal.absNorm v.asIdeal`. Assume every maximal ideal of $\mathcal{O}_L$ lying under $v$ has ramification index $1$ over $v$, and that the type of such ideals (the subtype of $w$ with $w$ under $v$) is a subsingleton. Let $a \neq b$ be units of $K_v$ and $m \in \mathbb{Z}$ with $\|a-b\| = q^{-m}$, and let $\alpha, \beta$ be units of $E = L \otimes_K K_v$. Two hypotheses link $\delta = \mathrm{diag}(\alpha,\beta)$ to $\gamma = \mathrm{diag}(a,b)$: the norm string $\prod_{i<[L:K]} (\sigma \otimes \mathrm{id})^{i}(\delta)$ equals the image of $\gamma$ under $\mathrm{GL}_2(K_v) \to \mathrm{GL}_2(E)$ induced by $x \mapsto 1 \otimes x$, and the $\sigma$-twisted centraliser of $\delta$ in $\mathrm{GL}_2(E)$ is the image of the centraliser of $\gamma$ in $\mathrm{GL}_2(K_v)$ under that same map. A lattice-counting hypothesis is assumed: if $\|a\| = \|b\| = 1$, then for every $\varpi \in K_v$ with $\|\varpi\| = q^{-1}$ and every $s \in \mathbb{N}$, the additive subgroup $O_E$ given by the range of `HeightOneSpectrum.tensorAdicCompletionIntegersTo` has relative index $q^{\min(s,\,m.\mathrm{toNat})}$ in the intersection of the preimages of $O_E$ under $y \mapsto (\sigma \otimes \mathrm{id})(y) - \beta\alpha^{-1} y$ and under $y \mapsto (1 \otimes \varpi^{s}) y$. Let $\tau'$ be a Haar measure, for the Borel structure, on the twisted centraliser of $\delta$, assigning mass $1$ to those of its elements lying in [`AutomorphicForm.semiLocalIntegralSet`](def/AutomorphicForm_TwistedOrbital.html#L136), i.e. matrices over $E$ whose entries and whose inverse's entries lie in the semi-local integers. If $J' \in \mathbb{C}$ is a $\sigma$-twisted weighted orbital integral at $\delta$ with respect to $\tau'$ of the indicator function of that integral set with value $1$, then $J' = 0$ unless $\|a\| = \|b\| = 1$, in which case $J' = [L:K] \cdot 2\log q \cdot \sum_{s=0}^{m.\mathrm{toNat}} s\,(q^{s} - q^{s}/q)$.
--
--   This is the local analytic computation, at a finite place unramified and inert in $L$, of the $\sigma$-twisted weighted orbital integral of the unit element of the Hecke algebra at a regular diagonal element, as it occurs in the twisted trace formula comparison for base change for $\mathrm{GL}(2)$. It is used by the companion statement in which the ramification hypothesis on the places above $v$ is removed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_relIndex_eq_of_subsingleton_extension.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_relIndex_eq_of_subsingleton_extension
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (hinert : Subsingleton (v.Extension (𝓞 L)))
    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b) (m : ℤ)
    (hm : ‖(a : v.adicCompletion K) - b‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-m))
    (α β : (L ⊗[K] v.adicCompletion K)ˣ)
    (hN : AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a b))
    (hT : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β) =
      (AutomorphicForm.localCentralizer K v (diagUnits2 a b)).map
        (AutomorphicForm.toTensorGL K L (v.adicCompletion K)))
    (hidx : ‖(a : v.adicCompletion K)‖ = 1 → ‖(b : v.adicCompletion K)‖ = 1 →
      ∀ ϖ : v.adicCompletion K, ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ → ∀ s : ℕ,
        (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range.toSubring.toAddSubgroup.relIndex
            (((HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L)
                    v).range.toSubring.toAddSubgroup.comap
                ((AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ).toAddMonoidHom -
                  AddMonoidHom.mulLeft
                    ((β * α⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K))) ⊓
              ((HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L)
                    v).range.toSubring.toAddSubgroup.comap
                (AddMonoidHom.mulLeft ((1 : L) ⊗ₜ[K] (ϖ ^ s))))) =
          Ideal.absNorm v.asIdeal ^ min s m.toNat)
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)))
    (hτ' : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ')
    (hτ'1 : τ' {t | (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈
      AutomorphicForm.semiLocalIntegralSet K L v} = 1)
    (J' : ℂ)
    (hJ' : AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ'
      ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) J') :
    J' = if ‖(a : v.adicCompletion K)‖ = 1 ∧ ‖(b : v.adicCompletion K)‖ = 1 then
        (Module.finrank K L : ℂ) *
          (((2 * Real.log (Ideal.absNorm v.asIdeal) *
              ∑ s ∈ Finset.range (m.toNat + 1),
                (s : ℝ) * ((Ideal.absNorm v.asIdeal : ℝ) ^ s -
                  (Ideal.absNorm v.asIdeal : ℝ) ^ s / (Ideal.absNorm v.asIdeal : ℝ)) : ℝ) : ℂ))
      else 0 := by sorry
