-- Prove2me | Theorems.Thm_BayesOptStop_Scheme_claim_1
-- name    : BayesOptStop.Scheme.claim_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:19:53.252083+00:00
-- url     : https://prove2.me/theorems/5ebc0a65-f800-4b13-a34b-916a150d7d34
-- title:
--   Claim 1 — the importance-sampling identity for $Z^{(j)}$
-- statement:
--   Let $W_j=\prod_{\ell=0}^{j-1}\max\{\alpha_\ell,\rho_\ell\}$. For every $j\ge0$, $t\in[n]$ and history $h_t$,
--   $$Z^{(j)}_t(h_t)=\mathbb E[M_0W_j\mid h_t]=Z^{(0)}_t(h_t)\cdot\mathbb E_*[W_j\mid h_t].$$
--
--   Differences from the source:
--   - generalization: α_ℓ are the ratios of Algorithm 2, started from α₀ = α ∈ (0,1) → any real α₀; reason: the identity follows from the recursions alone; the source's α₀ is a special case
--   - encoding: a history h_t → the history of a path ω at time t ∈ [1, n]; at a null history all three sides are 0; reason: the source's quantities are undefined at null histories; Lean's 0/0 = 0
--   - encoding: histories h_t are sequences of observed values; times t ∈ [n] are 1-based → paths ω : Fin n → Fin m of value indices, histories are value cylinders `Agree t` (first t values equal), times 0-based (the paper's X_t is X ⟨t-1⟩, Z_t at history length t); reason: Lean convention; conditioning is on values, so repeated v_q give the paper's filtration
--   - encoding: E_* is the expectation under Pr_*[· | F_t] of eq. (10) → `biasedExp`, the sum against the weights `biasedProb` = Pr[ω' | h_t] M_0(ω')/Z^(0)_t(h_t) on paths extending h_t; reason: the same finite measure
-- source:
--   AmaniHamedani, Aouad, Işık, Kesselheim, Saberi (2026), Bayesian Optimal Stopping: Invincible Prophets and Achievable Philosophers, held STOC 2027 submission, SHA-256 fecfa05a3285ac21a7efbed099d2afed88a382dfcc9d91836b6e5210d70c4241, Claim 1, p. 20 (proof App. B.1, pp. 37–38)

import Mathlib
import Definitions.Def_BayesOptStop_Scheme_Improvement

namespace BayesOptStop.Scheme

/-- **Claim 1** (AmaniHamedani, Aouad, Işık, Kesselheim, Saberi 2026, held STOC 2027 submission,
SHA-256 fecfa05a…c4241, p. 20): with `W_j = ∏_{ℓ<j} max{α_ℓ, ρ_ℓ}`, for every `j ≥ 0`, `t ∈ [n]`
and history `h_t`, `Z^(j)_t(h_t) = E[M_0 W_j | h_t] = Z^(0)_t(h_t) · E_*[W_j | h_t]`. -/
theorem claim_1 {K m n : ℕ} (I : Instance K m n) (hI : I.Valid) (hS : I.Standing) (α₀ : ℝ)
    (j t : ℕ) (ht1 : 1 ≤ t) (htn : t ≤ n) (ω : Fin n → Fin m) :
    I.Zseq α₀ j t ω = I.condExp (fun ω' => I.pathMax ω' * I.Wseq α₀ j ω') t ω ∧
      I.condExp (fun ω' => I.pathMax ω' * I.Wseq α₀ j ω') t ω =
        I.Zseq α₀ 0 t ω * I.biasedExp t ω (I.Wseq α₀ j) := by sorry

end BayesOptStop.Scheme
