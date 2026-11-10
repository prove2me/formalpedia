-- Prove2me | Theorems.Thm_BayesOptStop_Scheme_lemma_2
-- name    : BayesOptStop.Scheme.lemma_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:18:52.56799+00:00
-- url     : https://prove2.me/theorems/49eacab2-90dc-4f75-a957-36b7c7c2ed4c
-- title:
--   Lemma 2 — the dual update yields a dual martingale
-- statement:
--   Let $M$ be a dual certificate with Doob martingale $Z_t=\mathbb E[M\mid F_t]$, let $\rho=\max_{t\in[n]}X_t/Z_t$ and $M^+=M\max\{\rho,\alpha\}$. Then $Z^+_t=\mathbb E[M^+\mid F_t]$ is a dual martingale: a martingale with $Z^+_t\ge X_t$ almost surely for every $t\in[n]$.
--
--   Differences from the source:
--   - generalization: α is the competitiveness factor of the algorithm A in the input of the Primal-Dual Improvement → any real α, and no algorithm A; reason: neither the update nor the claim involves A; every source instance is an instance of the Lean statement
--   - encoding: histories h_t are sequences of observed values; times t ∈ [n] are 1-based → paths ω : Fin n → Fin m of value indices, histories are value cylinders `Agree t` (first t values equal), times 0-based (the paper's X_t is X ⟨t-1⟩, Z_t at history length t); reason: Lean convention; conditioning is on values, so repeated v_q give the paper's filtration
--   - encoding: conditional expectations and ratios X_t/Z_t at a zero-probability history or with Z_t = 0 are not defined → 0/0 = 0 and x/0 = 0 (Lean's division); reason: these cases are excluded by the source or have probability 0; the convention changes no statement about reachable histories
--   - encoding: almost surely → on every path of positive probability; reason: finite probability space; the same notion
--   - generalization: the horizon has at least one observation → n = 0 is also admitted; reason: all martingale and dominance conditions are empty at horizon zero
-- source:
--   AmaniHamedani, Aouad, Işık, Kesselheim, Saberi (2026), Bayesian Optimal Stopping: Invincible Prophets and Achievable Philosophers, held STOC 2027 submission, SHA-256 fecfa05a3285ac21a7efbed099d2afed88a382dfcc9d91836b6e5210d70c4241, Lemma 2, p. 14 (proof p. 15)

import Mathlib
import Definitions.Def_BayesOptStop_Scheme_Martingale

namespace BayesOptStop.Scheme

/-- **Lemma 2** (AmaniHamedani, Aouad, Işık, Kesselheim, Saberi 2026, held STOC 2027 submission,
SHA-256 fecfa05a…c4241, p. 14): for a dual certificate `M` with Doob martingale
`Z_t = E[M | F_t]`, `ρ = max_t X_t/Z_t` and `M⁺ = M · max{ρ, α}`, the process
`Z⁺_t = E[M⁺ | F_t]` is a dual martingale. -/
theorem lemma_2 {K m n : ℕ} (I : Instance K m n) (hI : I.Valid) (hS : I.Standing)
    (M : (Fin n → Fin m) → ℝ) (hM : I.IsDualCertificate M) (α : ℝ) :
    I.IsDualMartingale (I.doob (I.dualUpdate M α)) := by sorry

end BayesOptStop.Scheme
