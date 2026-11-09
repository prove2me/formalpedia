-- Prove2me | Theorems.Thm_DistributedMIS_LocalLowerBound_local_lower_bound_parameter_checks
-- name    : DistributedMIS.LocalLowerBound.local_lower_bound_parameter_checks
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:06.947242+00:00
-- url     : https://prove2.me/theorems/1db0d62b-d3b7-4656-997e-7d776fbd48c8
-- title:
--   Lemma A.6 — Parameter checks for the LOCAL lower bound
-- statement:
--   Fix 0<σ≤1 and an absolute degree threshold. Set D=⌊log n/4⌋, k=2⌈e^D/2⌉, N=2⌊n/(2k)⌋ and g=2T+8. For every ε>0 there is n₀, independent of T, such that whenever n≥n₀ and 0≤T<σ log n/(100000 log log n), a skeleton H exists satisfying every finite obstruction hypothesis, and
--
--   $$\delta_{ID}<\varepsilon,\qquad n\gamma_{EXT}<\varepsilon.$$
--
--   The statement also records proof support for fixed degree advice kD: its graph failure probability is at most β_ADV=2n exp(-k/(4D))<ε, uniformly over these skeletons and T. This follows from the binomial degree law and the concentration calculation in the moderation notes. These are quantified eventual bounds for every sufficiently large n.
--
--   Differences from the source:
--   - encoding: N named skeleton vertices, k named clique coordinates, isolated padding to n, and positive graph size → Fin N, Fin k, their disjoint sum with Fin (n-kN), and n≥1; reason: cardinality is exactly n under kN≤n; positivity excludes the undefined log₂ n convention, and legal identifiers are bijections to Fin n read as 1 through n
--   - encoding: uniform little-o estimates → for every positive ε, one eventual threshold for all admissible T; reason: this is the quantified definition of both uniform little-o assertions
--   - generalization: the particular absolute threshold D₀ of the paper → any prescribed natural degree threshold; reason: the asymptotic D tends to infinity and eventually exceeds every fixed bound
--   - generalization: A.6 states the ID and domination error limits; Theorem 1.1 also grants approximate degree information → add the uniform bound β_ADV for failure of Δ≤kD≤2Δ and its limit zero; reason: this supplies the unstated concentration step required by the goal information clause; the binomial calculation is given in MODERATION_NOTES.md
-- source:
--   Seri Khoury, Aaron Schild, STOC 2027 submission #411 (October 2026), pinned submission dated October 30, 2026; Lemma A.6, printed/PDF pp. 34

import Definitions.Def_DistributedMIS_LocalLowerBound_FiniteBlowup

namespace DistributedMIS.LocalLowerBound

theorem local_lower_bound_parameter_checks (σ : ℝ) (hσ : 0 < σ) (hσ₁ : σ ≤ 1) (D₀ : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, 3 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
    ∀ T : ℕ, (T : ℝ) < σ * Real.log n / (100000 * Real.log (Real.log n)) →
      let D := reductionD n
      let k := reductionK n
      let N := reductionN n
      (∃ H : SimpleGraph (Fin N), finiteParameters n D k N T D₀ H) ∧
      identifierError n D k T < ε ∧ (n : ℝ) * externalError D k < ε ∧
      degreeAdviceError n D k < ε ∧
      (∀ H : SimpleGraph (Fin N), finiteParameters n D k N T D₀ H →
        matrixProbability {ω : Matrices k | DegreeAdviceBad (n := n) D H ω} ≤
          degreeAdviceError n D k) := by sorry

end DistributedMIS.LocalLowerBound
