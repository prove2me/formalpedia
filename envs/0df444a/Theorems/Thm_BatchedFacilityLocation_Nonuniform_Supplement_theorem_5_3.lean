-- Prove2me | Theorems.Thm_BatchedFacilityLocation_Nonuniform_Supplement_theorem_5_3
-- name    : BatchedFacilityLocation.Nonuniform.Supplement.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:48:04.869211+00:00
-- url     : https://prove2.me/theorems/4a826bbb-5fb8-4733-b2d6-fe87c3dbf6f3
-- title:
--   Theorem 5.3 — batched lower bound $\Omega(\min\{\log(B+1),\sqrt{\log(n-B+2)}\})$ for every $n$ and $B$
-- statement:
--   There is an absolute constant $c>0$ with the following property. For all integers $n\ge1$ and $1\le B\le n$ there is a finite metric space $S$, fixed and known before the algorithm, with all opening costs equal to one, such that every randomized online algorithm on $S$ that sees each arriving batch in full has an instance on which it is expensive. Precisely: for every probability space $(\Omega,\mu)$ and every family $(A_\omega)_{\omega\in\Omega}$ of deterministic online algorithms with fully revealed batches (whose cost on each arrival sequence is a measurable function of $\omega$), there is an instance of exactly $n$ clients at sites of $S$ in exactly $B$ nonempty batches such that, with the batches arriving in uniformly random order independent of $\omega$,
--
--   $$
--   \mathbb E[\mathrm{ALG}]\ \ge\ c\,\min\Big\{\log(B+1),\sqrt{\log(n-B+2)}\Big\}\cdot\mathrm{OPT}.
--   $$
--
--   Here $\mathrm{ALG}$ counts the facilities opened plus, for every client, its distance to the facilities open by the end of its own batch, and $\mathrm{OPT}$ is the offline optimum with unit opening costs. So every randomized algorithm has competitive ratio $\Omega(\min\{\log(B+1),\sqrt{\log(n-B+2)}\})$, already with uniform costs, which shows that the goal's bound (Theorem 4.1) and Theorem 3.1 are tight up to constants.
--
--   Differences from the source:
--   - encoding: competitive ratio at least Ω(min{log(B+1), √log(n−B+2)}) → ∃ c > 0 such that for every algorithm some instance has c · min{…} · OPT ≤ E[ALG]; reason: the ratio is written multiplicatively; the proof gives E[ALG] ≥ h/6, OPT ≤ 9/4 for h ≥ 4 and ALG ≥ OPT for h < 4, so the constant is absolute
--   - generalization: for every randomized algorithm there is a hard instance (on the paper's known tree) → the finite metric S is chosen before the algorithm, and the instance on S after it; reason: §5 (p. 24) states that the tree is known in advance; ∃ S ∀ A ∃ I implies ∀ A ∃ (S, I)
--   - generalization: online algorithms that serve each fully revealed batch before the next arrives → any rule A choosing openings from the revealed batches, charged |O_B| + Σ_k Σ_{x∈L_k} d(x, O_k) with O_k the facilities open by the end of batch k; reason: every such algorithm pays at least this charge for its openings, and the class allows every use of the revealed batch, so a lower bound on it is a lower bound for the source's algorithms
--   - encoding: a randomized algorithm → a probability space (Ω, μ) in an arbitrary universe and a family A_ω, with ω ↦ cost(A_ω, L) measurable for each L, its randomness independent of the batch order; reason: this is a randomized algorithm whose cost is a random variable; no restriction to finite support
--   - encoding: with uniform costs, and therefore also with nonuniform costs → all opening costs equal to one; reason: the hard instance of §5 has unit costs (p. 24), and the uniform and nonuniform models contain it
--   - encoding: n clients in B batches → an instance I with I.Valid, I.n = n and I.B = B (exactly n clients, exactly B nonempty batches); reason: the theorem is for every n and B (p. 25–26: 'exactly n clients and B batches')
--   - encoding: n − B → ((n - B : ℕ) : ℝ); reason: B ≤ n is a hypothesis, so the natural-number subtraction is exact
--   - reading: log (base unspecified) → Real.log (natural logarithm); reason: a change of base only changes the constant
-- source:
--   Fabrizio Grandoni, Stefano Leonardi, Matteo Russo, Metric Facility Location under Batched Random Order, STOC 2027 submission #212 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/212.pdf (source.pdf sha256 2e976c4133df9baa0c32b4cd22b6e370c2c4611dfe4d4dec02ceb01bd7a0dc94), Theorem 5.3, p. 25 (setting §5 p. 24, proof p. 25–26 via Lemmas 5.1, 5.2)

import Mathlib
import Definitions.Def_BatchedFacilityLocation_Nonuniform_Supplement_LowerBound

open MeasureTheory
open scoped ENNReal

namespace BatchedFacilityLocation.Nonuniform.Supplement

universe u

/-- Theorem 5.3 (Batched lower bound for every `n` and `B`, p. 25). There is an absolute
constant `c > 0` such that for every `n ≥ 1` and `1 ≤ B ≤ n` there is a finite metric `S`
(known in advance; all opening costs one) such that every randomized online algorithm on `S`
that sees each arriving batch in full has, on some instance of exactly `n` clients in exactly
`B` nonempty batches arriving in uniformly random order,
`E[ALG] ≥ c · min {log (B + 1), √(log (n - B + 2))} · OPT`. -/
theorem theorem_5_3 :
    ∃ c : ℝ, 0 < c ∧ ∀ n B : ℕ, 1 ≤ B → B ≤ n →
      ∃ (S : Type) (_ : Fintype S) (_ : MetricSpace S),
        ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (A : Ω → List (List S) → Finset S),
          (∀ L : List (List S), Measurable fun ω => detCost (A ω) L) →
          ∃ I : Instance S, I.Valid ∧ I.n = n ∧ I.B = B ∧
            ENNReal.ofReal (c * min (Real.log (B + 1))
                (Real.sqrt (Real.log (((n - B : ℕ) : ℝ) + 2)))) * OPT (fun _ => 1) I.loc ≤
              brExp (fun L => ∫⁻ ω, detCost (A ω) L ∂μ) I := by sorry

end BatchedFacilityLocation.Nonuniform.Supplement
