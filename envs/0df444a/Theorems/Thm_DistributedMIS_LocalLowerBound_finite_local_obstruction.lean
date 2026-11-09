-- Prove2me | Theorems.Thm_DistributedMIS_LocalLowerBound_finite_local_obstruction
-- name    : DistributedMIS.LocalLowerBound.finite_local_obstruction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:18.872562+00:00
-- url     : https://prove2.me/theorems/755d4143-6e09-4318-8f22-12cbe238a50e
-- title:
--   Proposition 3.1 — Finite LOCAL obstruction
-- statement:
--   Let H be a simple D-regular N-vertex skeleton with girth at least 2T+8, kN≤n, even k, D≥D₀, D≤log k≤D², and k b_ID≤⌊k²/4⌋, where b_ID=⌈log₂ n⌉. Use the stated L, δ_ID and γ_EXT. If a measurable T-round LOCAL program succeeds with probability at least σ>0 on every legal n-vertex input, then
--
--   $$\sigma(1-\delta_{ID}-\gamma_{EXT})\le\min\{1,5000(T+3)\log D/D\}.$$
--
--   This is the unhinted finite obstruction exactly as printed. Degree-advice failures are handled separately in the final goal's reduction and are not silently inserted into this formula.
--
--   Differences from the source:
--   - encoding: N named skeleton vertices, k named clique coordinates, isolated padding to n, and positive graph size → Fin N, Fin k, their disjoint sum with Fin (n-kN), and n≥1; reason: cardinality is exactly n under kN≤n; positivity excludes the undefined log₂ n convention, and legal identifiers are bijections to Fin n read as 1 through n
--   - encoding: finite conditional probabilities of independent fair edge matrices → exact uniform cylinder sums with transposed reverse orientations; reason: only the finitely many required edge variables are averaged; this is the marginal of the infinite fair product law, with arbitrary finite radius retained
--   - encoding: arbitrary synchronous LOCAL computation and unbounded messages with independent infinite private tapes → one uniform full-state initialization, transition and output program, with total executions; reason: a state can store the original state, tape, round and port table, so every per-port message can be reconstructed from the full-state broadcast; programs may be chosen separately for each n and may idle until T
--   - encoding: one unspecified sufficiently large absolute D₀ → an existential absolute threshold before D, k, radius and rule; reason: the finitely many thresholds can be unified by their maximum; none depends on the radius or rule
--   - encoding: the unhinted LOCAL program of Proposition 3.1 → CorrectAtAdvice with its otherwise unused advice input fixed to zero; reason: fixing this argument represents precisely the unhinted program class of the proposition; the goal separately allows all legal degree advice
-- source:
--   Seri Khoury, Aaron Schild, STOC 2027 submission #411 (October 2026), pinned submission dated October 30, 2026; Proposition 3.1, printed/PDF pp. 9–10

import Definitions.Def_DistributedMIS_LocalLowerBound_FiniteBlowup

namespace DistributedMIS.LocalLowerBound

theorem finite_local_obstruction : ∃ D₀ : ℕ, 3 ≤ D₀ ∧ ∀ (n D k N T : ℕ) (hn : 1 ≤ n)
    (H : SimpleGraph (Fin N)) (hH : finiteParameters n D k N T D₀ H)
    (P : LocalProgram) (hP : MeasurableProgram P) (σ : ℝ) (hσ : 0 < σ)
    (hcorrect : CorrectAtAdvice P n 0 T σ),
    σ * (1 - identifierError n D k T - externalError D k) ≤
      min 1 (5000 * (T+3) * Real.log D / D) := by sorry

end DistributedMIS.LocalLowerBound
