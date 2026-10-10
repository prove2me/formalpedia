-- Prove2me | Theorems.Thm_BlindProphetSec_Blind_lemma_4_1
-- name    : BlindProphetSec.Blind.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:38:21.87124+00:00
-- url     : https://prove2.me/theorems/d271e00c-9177-49e0-b502-0efe4bdd25ae
-- title:
--   Lemma 4.1, p. 12 — P(T ≥ k | σ_k = i) ≥ P(T > k) / (1 − k/n + (1/n) Σ_{l∈[k]} P(Vᵢ ≤ τ_l)) for nonincreasing thresholds
-- statement:
--   Let $V_1,\dots,V_n$ be independent random variables arriving in uniformly random order $\sigma$, let $\tau_1\ge\dots\ge\tau_n$ be nonincreasing thresholds, and let $T$ be the stopping time of $\mathrm{TTA}_{\tau_1,\dots,\tau_n}$. Then for all $i,k\in[n]$,
--   $$\mathbb P(T\ge k\mid\sigma_k=i)\;\ge\;\frac{\mathbb P(T>k)}{1-\frac kn+\frac1n\sum_{l\in[k]}\mathbb P(V_i\le\tau_l)}.$$
--
--   This sharpens the inequality $\mathbb P(T\ge k\mid\sigma_k=i)\ge\mathbb P(T>k)$ of Lemma 3.2 and is the key new ingredient of the 0.669 analysis.
--
--   **Formalization Note.** The inequality is stated multiplied out, $\mathbb P(T>k)\le n\,\mathbb P(T\ge k,\sigma_k=i)\cdot\big(1-\frac kn+\frac1n\sum_{l\in[k]}\mathbb P(V_i\le\tau_l)\big)$, with the conditional probability in joint form ($\mathbb P(\sigma_k=i)=1/n$). This is equivalent when the denominator is positive; it vanishes only when $k=n$ and $\mathbb P(V_i\le\tau_l)=0$ for all $l$, and then $\mathbb P(T>n)=0$ because $V_i$ is accepted whenever it arrives, so the multiplied form is still the paper's claim. The index $k$ is 0-based in Lean (`k : Fin n`, paper's $k$ = `k.val + 1`). Nonnegativity and continuity are not assumed, as on the page.
-- source:
--   Correa, Saona & Ziliotto, Prophet Secretary Through Blind Strategies, arXiv:1807.07483v2, p. 12, Lemma 4.1

import Mathlib
import Definitions.Def_BlindProphetSec_Blind_Setting

namespace BlindProphetSec.Blind

open MeasureTheory

theorem lemma_4_1 {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (τ : Fin n → ℝ) (hτ : Antitone τ) (i k : Fin n) :
    probVS μ (fun v σ => ¬ stopLE (ttaAcc τ v σ) (k.val + 1)) ≤
      ((n : ℝ) * probVS μ (fun v σ => stopGE (ttaAcc τ v σ) (k.val + 1) ∧ σ k = i)) *
        (1 - ((k.val : ℝ) + 1) / n +
          (1 / (n : ℝ)) * ∑ l ∈ Finset.univ.filter (fun l : Fin n => l.val ≤ k.val),
            (μ i (Set.Iic (τ l))).toReal) := by sorry

end BlindProphetSec.Blind
