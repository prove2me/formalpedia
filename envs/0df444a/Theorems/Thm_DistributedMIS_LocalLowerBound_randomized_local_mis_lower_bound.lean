-- Prove2me | Theorems.Thm_DistributedMIS_LocalLowerBound_randomized_local_mis_lower_bound
-- name    : DistributedMIS.LocalLowerBound.randomized_local_mis_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:41:11.20558+00:00
-- url     : https://prove2.me/theorems/28561ff1-0c54-4633-bd03-02b24fff7f1f
-- title:
--   Theorem 1.1 — Randomized LOCAL MIS lower bound
-- statement:
--   Fix a success probability 0<σ≤1. There exist c_σ>0 and n_σ such that, for every integer n≥n_σ, every measurable randomized LOCAL program that produces an entire maximal independent set with probability at least σ on every legal n-vertex graph needs at least
--
--   $$c_\sigma\frac{\log n}{\log\log n}$$
--
--   worst-case communication rounds. The program knows n exactly, uses the identifier set [n] and arbitrary legal port orderings, sees degrees and neighbor identifiers initially, and receives constant-factor degree advice Δ≤Δ̂≤2Δ, required to work for every legal value. Every vertex has an independent infinite private fair-bit tape. Programs may be chosen nonuniformly for each n; runtime is bounded on every tape realization. The paper writes an existential c_σ; its proof yields c_σ=σ/100000 for sufficiently large n.
--
--   This is the full headline theorem, including the information-advantage clause after the display. It concerns global independence and inclusion-maximality, not a per-vertex success guarantee.
--
--   Differences from the source:
--   - encoding: arbitrary synchronous LOCAL computation and unbounded messages with independent infinite private tapes → one uniform full-state initialization, transition and output program, with total executions; reason: a state can store the original state, tape, round and port table, so every per-port message can be reconstructed from the full-state broadcast; programs may be chosen separately for each n and may idle until T
--   - encoding: identifiers exactly [n], arbitrary legal ports and constant-factor maximum-degree information → permutations of Fin n read as 1 through n, arbitrary ordered neighbor lists, and every Δ̂ with Δ≤Δ̂≤2Δ; reason: port indices are the list positions; the factor two makes the fixed constant-factor convention explicit and enforces advice zero at degree zero
--   - encoding: existential c_σ and eventual n_σ → retain the existential witnesses, record c_σ=σ/100000, and take n_σ≥3; reason: p. 10 supplies that exact witness and n≥3 makes both logarithms positive; thresholds precede all programs and T
-- source:
--   Seri Khoury, Aaron Schild, STOC 2027 submission #411 (October 2026), pinned submission dated October 30, 2026; Theorem 1.1 and following information clause, printed/PDF p. 3; proof p. 10; Appendix A.5, pp. 34–35

import Definitions.Def_DistributedMIS_LocalLowerBound_LocalPrograms

namespace DistributedMIS.LocalLowerBound

theorem randomized_local_mis_lower_bound (σ : ℝ) (hσ : 0 < σ) (hσ₁ : σ ≤ 1) :
    ∃ cσ : ℝ, 0 < cσ ∧ cσ = σ / 100000 ∧ ∃ nσ : ℕ, 3 ≤ nσ ∧
    ∀ n : ℕ, nσ ≤ n → ∀ (P : LocalProgram) (T : ℕ),
      MeasurableProgram P → CorrectWithAdvice P n T σ →
        cσ * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) ≤ (T : ℝ) := by sorry

end DistributedMIS.LocalLowerBound
