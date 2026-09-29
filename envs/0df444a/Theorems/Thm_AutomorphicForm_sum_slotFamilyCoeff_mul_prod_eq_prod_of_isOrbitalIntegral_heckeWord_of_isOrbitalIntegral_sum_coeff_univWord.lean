-- Prove2me | Theorems.Thm_AutomorphicForm_sum_slotFamilyCoeff_mul_prod_eq_prod_of_isOrbitalIntegral_heckeWord_of_isOrbitalIntegral_sum_coeff_univWord
-- name    : AutomorphicForm.sum_slotFamilyCoeff_mul_prod_eq_prod_of_isOrbitalIntegral_heckeWord_of_isOrbitalIntegral_sum_coeff_univWord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/c89fac8f-b019-5793-9d09-0d03835b32e7
-- title:
--   Slot regrouping of Hecke-word orbital integrals
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, fix for every finite place $v$ of $K$ (a height-one prime of $\mathcal{O}_K$) an extension $w_v =$ `ws v`, i.e. a height-one prime of $\mathcal{O}_L$ lying under $v$, and let $T$ be a finite set of finite places of $K$. Fix data indexed by the places of $K$: naturals $n_v =$ `nKs v`, elements $r_{v,i} \in \mathrm{GL}_2(K_v)$ for $i \in \mathrm{Fin}\,n_v$, an element $z_v \in \mathrm{GL}_2(K_v)$, naturals $k_v$, $j_v$, and elements $\gamma_v \in \mathrm{GL}_2(K_v)$ which for $v \in T$ are regular semisimple in the sense that $\operatorname{tr}(\gamma_v)^2 - 4\det(\gamma_v)$ is a unit. For each $v$ let $\tau_v$ be a Borel measure on the centraliser of $\gamma_v$ in $\mathrm{GL}_2(K_v)$, assumed for $v \in T$ to be Haar and to give mass $1$ to the part of the centraliser lying in the local integral set `localIntegralSet` (matrices in $\mathrm{GL}_2(K_v)$ whose entries and whose inverse's entries lie in $\mathcal{O}_{K_v}$). Two families of complex numbers are given. First, $I_W(m,v)$, indexed by $v$ and by $m$ in `slotIndex K L ws ks js T` — the set of families $m$ assigning to each $v \in T$ an exponent vector in $\mathrm{Fin}\,2 \to_{f} \mathbb{N}$ lying in the support of `slotWord K L ws v (ks v) (js v)` — subject to the hypothesis that for every such $m$ and every $v \in T$, $I_W(m,v)$ is an orbital integral of $\gamma_v$ with respect to $\tau_v$ of the local test function $x \mapsto \sum_{\iota : \mathrm{Fin}\,(m_v 0) \to \mathrm{Fin}\,n_v} \mathbf{1}_{\mathrm{localIntegralSet}}\big((\prod_i r_{v,\iota(i)} \cdot z_v^{m_v 1})^{-1} x\big)$; here being an orbital integral of $f$ with value $I$ means that there is a nonnegative measurable compactly supported weight $w$ with $\int_{Z(\gamma_v)} w(tx)\,d\tau_v = 1$ whenever $f(x^{-1}\gamma_v x) \neq 0$, and $I = \int f(x^{-1}\gamma_v x)\,w(x)\,d(\mathrm{localHaar})$. Second, $I_T(v)$ for $v \in T$, assumed to be the orbital integral of $\gamma_v$ with respect to $\tau_v$ of the linear combination $x \mapsto \sum_{r} c_r\, N(v)^{r 1} / N(w_v)^{j_v} \sum_{\iota : \mathrm{Fin}\,(r 0) \to \mathrm{Fin}\,n_v} \mathbf{1}_{\mathrm{localIntegralSet}}\big((\prod_i r_{v,\iota(i)} \cdot z_v^{r 1})^{-1} x\big)$, the sum being over the support of the polynomial `univWord` $(f-1, k_v, j_v) = \mathrm{satakePow}_{f}(X_0,X_1)^{k_v} \cdot (X_1^{f})^{j_v}$ with $f =$ `inertiaDeg'` of $v$ in $w_v$, $c_r$ its coefficients, and $N$ the absolute ideal norm. The conclusion is that $\sum_{m} \big(\prod_{v \in T} \mathrm{slotCoeff}(v, k_v, j_v, m_v)\big) \prod_{v \in T} I_W(m,v) = \prod_{v \in T} I_T(v)$, the sum running over `slotIndex K L ws ks js T`.
--
--   The identity records that the slot decomposition of a Hecke word at the places of $T$ is compatible with taking local orbital integrals: since the slot index set is a product over $T$ and the slot family coefficient a product of per-place coefficients, the weighted sum over slot members of products of member-wise orbital integrals collapses to the product over $T$ of the orbital integrals of the per-place coefficient combinations. It is used in the winding-datum form of the comparison of hyperbolic terms, where it converts member-indexed products into member-free ones.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_sum_slotFamilyCoeff_mul_prod_eq_prod_of_isOrbitalIntegral_heckeWord_of_isOrbitalIntegral_sum_coeff_univWord.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_LocalLanglands_HeckeCosetSystem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

theorem AutomorphicForm.sum_slotFamilyCoeff_mul_prod_eq_prod_of_isOrbitalIntegral_heckeWord_of_isOrbitalIntegral_sum_coeff_univWord
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (nKs : HeightOneSpectrum (𝓞 K) → ℕ)
    (rKs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (nKs v) → GL (Fin 2) (v.adicCompletion K))
    (zKs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K))
    (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
    (γ : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K))
    (hγ : ∀ v ∈ T, AutomorphicForm.IsRegularSemisimple (γ v))
    (τ : ∀ v : HeightOneSpectrum (𝓞 K),
      @Measure (AutomorphicForm.localCentralizer K v (γ v)) (AutomorphicForm.localCentralizerBorel K v (γ v)))
    (hτ : ∀ v ∈ T, @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (γ v)) (τ v))
    (hτ1 : ∀ v ∈ T, τ v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (IW : ((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIW : ∀ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T,
      ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
        AutomorphicForm.IsOrbitalIntegral K v (γ v) (τ v) (fun x : GL (Fin 2) (v.adicCompletion K) =>
            ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
              (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (m v hv) 1)⁻¹ * x)) (IW m v))
    (IT : HeightOneSpectrum (𝓞 K) → ℂ)
    (hIT : ∀ v ∈ T, AutomorphicForm.IsOrbitalIntegral K v (γ v) (τ v) (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ r ∈ (AutomorphicForm.SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).support,
          (AutomorphicForm.SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).coeff r *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (r 1) / (Ideal.absNorm (ws v).1.asIdeal : ℂ) ^ (js v) *
            ∑ ι : Fin (r 0) → Fin (nKs v),
              (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (r 1))⁻¹ * x)) (IT v)) :
    ∑ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T,
        AutomorphicForm.SatakeCombination.slotFamilyCoeff K L ws ks js T m * ∏ v ∈ T, IW m v =
      ∏ v ∈ T, IT v := by sorry
