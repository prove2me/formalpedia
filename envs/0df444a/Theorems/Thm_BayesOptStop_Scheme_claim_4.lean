-- Prove2me | Theorems.Thm_BayesOptStop_Scheme_claim_4
-- name    : BayesOptStop.Scheme.claim_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:19:54.744684+00:00
-- url     : https://prove2.me/theorems/e5400978-7f28-42b4-85e0-40a02e2ef451
-- title:
--   Claim 4 — Monte Carlo estimation of $Z^{(j)}_t$ under the biased measure
-- statement:
--   Let $j\ge1$, $t\in[n]$, a fixed history $h_t$ and $G_{j-1}=\prod_{\ell<j}\alpha_\ell$. Given $r$ independent samples $\omega^{(i)}$ from $\Pr_*[\cdot\mid h_t]$ and, for each $i$, an estimate $\widehat W_j(\omega^{(i)})$ with $\widehat W_j(\omega^{(i)})/W_j(\omega^{(i)})\in[1-\eta,(1-\eta)^{-1}]$ with probability at least $1-\kappa$ conditionally on every realized $\omega^{(i)}$ ($0<\eta,\kappa<1$), the estimate $\widehat Z^{(j)}_t(h_t)=Z^{(0)}_t(h_t)\cdot\frac1r\sum_i\widehat W_j(\omega^{(i)})$ satisfies $\widehat Z^{(j)}_t(h_t)/Z^{(j)}_t(h_t)\in[(1-\eta)^2,(1-\eta)^{-2}]$ with probability at least $1-\kappa r-2\exp(-\eta^2rG_{j-1}/3)$.
--
--   Differences from the source:
--   - reading: Claim 4 states no range for α₀ → 0 < α₀ ≤ 1; reason: the α_ℓ are those of Algorithm 2 in App. B.3–B.5, where Claim 3 assumes 0 < α₀ ≤ 1 and Lemma 4 assumes 0 < α₀ < 1; the weaker of the two
--   - encoding: r independent samples of the continuation X_{t+1..n} from Pr_*[· | h_t] → random full paths S_i (h_t followed by the continuation), measurable and mutually independent (iIndepFun), each with P(S_i = ω') = Pr_*[ω' | h_t]; reason: the continuation concatenated with h_t is the sample path
--   - encoding: conditionally on every realized ω^(i), the ratio bound holds with probability ≥ 1 − κ → P(S_i = ω' and the bound fails) ≤ κ · P(S_i = ω') for every ω'; the What i are measurable; no independence of the estimates is assumed; reason: conditioning on a discrete variable; the source assumes nothing more
--   - encoding: a fixed history h_t → the history at time t of a path ω with Pr[h_t] > 0; reason: Pr_* is undefined at a null history
--   - encoding: ratios Ŵ/W and Ẑ/Z lie in an interval → products: a·W ≤ Ŵ ≤ b·W and a·Z ≤ Ẑ ≤ b·Z; reason: W_j ≥ G_{j-1} > 0, and Z^(j)_t(h_t) > 0 at a reachable history under the standing assumption
--   - encoding: histories h_t are sequences of observed values; times t ∈ [n] are 1-based → paths ω : Fin n → Fin m of value indices, histories are value cylinders `Agree t` (first t values equal), times 0-based (the paper's X_t is X ⟨t-1⟩, Z_t at history length t); reason: Lean convention; conditioning is on values, so repeated v_q give the paper's filtration
--   - generalization: the empirical average uses a positive number r of samples → r = 0 is also admitted with division by zero equal to zero; reason: at r = 0 the claimed probability lower bound is −1, so the additional case is automatic
-- source:
--   AmaniHamedani, Aouad, Işık, Kesselheim, Saberi (2026), Bayesian Optimal Stopping: Invincible Prophets and Achievable Philosophers, held STOC 2027 submission, SHA-256 fecfa05a3285ac21a7efbed099d2afed88a382dfcc9d91836b6e5210d70c4241, Claim 4, p. 39 (proof App. B.5, pp. 44–45)

import Mathlib
import Definitions.Def_BayesOptStop_Scheme_Improvement

open MeasureTheory ProbabilityTheory

namespace BayesOptStop.Scheme

/-- **Claim 4** (AmaniHamedani, Aouad, Işık, Kesselheim, Saberi 2026, held STOC 2027 submission,
SHA-256 fecfa05a…c4241, p. 39): for `j ≥ 1`, `t ∈ [n]`, a fixed history `h_t` and
`G_{j-1} = ∏_{ℓ<j} α_ℓ`, given `r` independent samples `ω^(i)` from `Pr_*[· | h_t]` and estimates
`Ŵ_j(ω^(i))` with `Ŵ_j(ω^(i))/W_j(ω^(i)) ∈ [1-η, (1-η)^{-1}]` with probability at least `1-κ`
conditionally on every realized `ω^(i)`, the estimate `Ẑ^(j)_t(h_t) = Z^(0)_t(h_t) · (1/r) ∑ Ŵ_j(ω^(i))`
satisfies `Ẑ^(j)_t(h_t)/Z^(j)_t(h_t) ∈ [(1-η)², (1-η)^{-2}]` with probability at least
`1 - κr - 2 exp(-η² r G_{j-1}/3)`. -/
theorem claim_4 {K m n : ℕ} (I : Instance K m n) (hI : I.Valid) (hS : I.Standing)
    (α₀ : ℝ) (hα0 : 0 < α₀) (hα1 : α₀ ≤ 1) (j : ℕ) (hj : 1 ≤ j) (t : ℕ) (ht1 : 1 ≤ t)
    (htn : t ≤ n) (ω : Fin n → Fin m) (hω : 0 < I.cylProb t ω)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r : ℕ) (S : Fin r → Ω → (Fin n → Fin m)) (What : Fin r → Ω → ℝ)
    (hSm : ∀ i, Measurable (S i)) (hWm : ∀ i, Measurable (What i)) (hind : iIndepFun S P)
    (hlaw : ∀ i ω', P.real {x | S i x = ω'} = I.biasedProb t ω ω')
    (η κ : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hest : ∀ i ω', P.real {x | S i x = ω' ∧
        ¬ ((1 - η) * I.Wseq α₀ j ω' ≤ What i x ∧ What i x ≤ (1 - η)⁻¹ * I.Wseq α₀ j ω')} ≤
      κ * P.real {x | S i x = ω'}) :
    1 - κ * r - 2 * Real.exp (-(η ^ 2 * r * Gprod α₀ j) / 3) ≤
      P.real {x | (1 - η) ^ 2 * I.Zseq α₀ j t ω ≤ I.Zseq α₀ 0 t ω * ((∑ i, What i x) / r) ∧
        I.Zseq α₀ 0 t ω * ((∑ i, What i x) / r) ≤ ((1 - η) ^ 2)⁻¹ * I.Zseq α₀ j t ω} := by sorry

end BayesOptStop.Scheme
