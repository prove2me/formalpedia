-- Prove2me | Theorems.Thm_CompetingKS_appendix_A_normalization
-- name    : CompetingKS.appendix_A_normalization
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:17:24.120655+00:00
-- url     : https://prove2.me/theorems/e4e89d60-00bd-4042-bc40-2d0191a491cc
-- title:
--   Appendix A — the normalization $a=b=1$, $c=0$ for profits, responses and equilibria
-- statement:
--   Let $a>c$, $b>0$, $\eta\in[0,1]$, and put $\varphi(w)=c+(a-c)w$ and $k=(a-c)^2/b$. The map $\varphi$ carries $[0,1]$ onto the contract space $[c,a]$. In the one-to-two channel, and in the two-to-one channel if $\eta<1$:
--
--   1. every profit at $(\varphi(w_i),\varphi(w_j))$ of the model with parameters $(a,b,c,\eta)$ is $k$ times the corresponding profit at $(w_i,w_j)$ of the model with parameters $(1,1,0,\eta)$, and so is the disagreement point of the common party;
--   2. $\varphi(w_i)$ is a Kalai–Smorodinsky response, or a Nash bargaining response with power $\theta\in[0,1]$, to $\varphi(w_j)$ in the general model if and only if $w_i$ is one to $w_j$ in the normalized model;
--   3. $(\varphi(w_1),\varphi(w_2))$ is a simultaneous equilibrium of the general model if and only if $(w_1,w_2)$ is one of the normalized model, for both solution concepts.
--
--   This is the bridge between the online appendix, which works at $a=b=1$, $c=0$, and the general statement of Proposition 2.
--
--   Differences from the source:
--   - reading: "the corresponding wholesale price would be c + (a − c)w" → φ(w) = c + (a − c)w carries the KS and NB responses and the simultaneous equilibria of the normalized model onto those of the general one; reason: this is the content of "without loss of generality"; the paragraph states it for profits and prices
--   - encoding: η ∈ [0, 1] for the two-to-one channel → η ∈ [0, 1); reason: at η = 1, wᵢ = wⱼ < a Lemma 1(ii)(a) gives q*ᵢ = 0 and (ii)(c) gives q*ᵢ = (a − wᵢ)/(2b), and (ii)(b) divides by 1 − η² = 0, so q* and the profits are undefined there; this excludes only that undefined case
-- source:
--   Feng, Li, Shanthikumar, Negotiations in Competing Supply Chains: The Kalai-Smorodinsky Bargaining Solution, accepted manuscript (Management Science, July 3, 2021), SSRN 3447674, Appendix A, online appendix p.2

import Mathlib
import Definitions.Def_CompetingKS_unitOT

namespace CompetingKS

/-- The normalization of Appendix A, Feng, Li, Shanthikumar, *Negotiations in Competing Supply
Chains: The Kalai-Smorodinsky Bargaining Solution*, accepted manuscript (Management Science, July
3, 2021), SSRN 3447674, online appendix p.2.

With `φ(w) = c + (a - c)w` and `k = (a - c)²/b`: every profit and disagreement point of the model
with parameters `(a, b, c, η)` at `(φ wᵢ, φ wⱼ)` is `k` times that of the model with parameters
`(1, 1, 0, η)` at `(wᵢ, wⱼ)`, and `φ` carries the responses and the simultaneous equilibria of the
normalized model onto those of the general model, in both channels. The contract space `[0, 1]` is
carried onto `[c, a]`.

**Formalization Note** The two-to-one part carries `η < 1`, the range on which the channel is
defined (see `qTO`). -/
theorem appendix_A_normalization {a b c η : ℝ} (hac : c < a) (hb : 0 < b) (hη₀ : 0 ≤ η)
    (hη₁ : η ≤ 1) :
    (fun w : ℝ => c + (a - c) * w) '' Set.Icc 0 1 = Set.Icc c a ∧
    ((∀ wi wj : ℝ,
        supplierOT a b c η (c + (a - c) * wi) (c + (a - c) * wj) =
          (a - c) ^ 2 / b * supplierOT 1 1 0 η wi wj ∧
        retailerOT a b η (c + (a - c) * wi) (c + (a - c) * wj) =
          (a - c) ^ 2 / b * retailerOT 1 1 η wi wj) ∧
      (∀ wj : ℝ, disagreeOT a b c η (c + (a - c) * wj) = (a - c) ^ 2 / b * disagreeOT 1 1 0 η wj) ∧
      (∀ wi wj : ℝ, (unitOT a b c η (c + (a - c) * wj)).IsKSResponse (c + (a - c) * wi) ↔
        (normOT η wj).IsKSResponse wi) ∧
      (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ wi wj : ℝ,
        (unitOT a b c η (c + (a - c) * wj)).IsNBResponse θ (c + (a - c) * wi) ↔
          (normOT η wj).IsNBResponse θ wi) ∧
      (∀ w₁ w₂ : ℝ, IsKSEqOT a b c η (c + (a - c) * w₁) (c + (a - c) * w₂) ↔
        IsKSEqOT 1 1 0 η w₁ w₂) ∧
      (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ w₁ w₂ : ℝ,
        IsNBEqOT a b c η θ (c + (a - c) * w₁) (c + (a - c) * w₂) ↔
          IsNBEqOT 1 1 0 η θ w₁ w₂)) ∧
    (η < 1 →
      (∀ wi wj : ℝ,
        supplierTO a b c η (c + (a - c) * wi) (c + (a - c) * wj) =
          (a - c) ^ 2 / b * supplierTO 1 1 0 η wi wj ∧
        retailerTO a b η (c + (a - c) * wi) (c + (a - c) * wj) =
          (a - c) ^ 2 / b * retailerTO 1 1 η wi wj) ∧
      (∀ wj : ℝ, disagreeTO a b η (c + (a - c) * wj) = (a - c) ^ 2 / b * disagreeTO 1 1 η wj) ∧
      (∀ wi wj : ℝ, (unitTO a b c η (c + (a - c) * wj)).IsKSResponse (c + (a - c) * wi) ↔
        (normTO η wj).IsKSResponse wi) ∧
      (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ wi wj : ℝ,
        (unitTO a b c η (c + (a - c) * wj)).IsNBResponse θ (c + (a - c) * wi) ↔
          (normTO η wj).IsNBResponse θ wi) ∧
      (∀ w₁ w₂ : ℝ, IsKSEqTO a b c η (c + (a - c) * w₁) (c + (a - c) * w₂) ↔
        IsKSEqTO 1 1 0 η w₁ w₂) ∧
      (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ w₁ w₂ : ℝ,
        IsNBEqTO a b c η θ (c + (a - c) * w₁) (c + (a - c) * w₂) ↔
          IsNBEqTO 1 1 0 η θ w₁ w₂)) := by sorry

end CompetingKS
