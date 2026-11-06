-- Prove2me | Theorems.Thm_BorelRobustMDP_remark_3_2_a
-- name    : BorelRobustMDP.remark_3_2_a
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:15:32.85788+00:00
-- url     : https://prove2.me/theorems/8ef8939a-eae6-401e-b98f-4864c90b13d4
-- title:
--   Remark 3.2 (a) — the bounding function controls $|c_n|$ and $b$ under every $Q$
-- statement:
--   Under Assumption 3.1 (i), for all $n<N$, $Q\in\mathcal Q_{n+1}$ and $(x,a)\in D_n$,
--
--   $$\mathbb E^Q\big[|c_n(x,a,T_n(x,a,Z_{n+1}))|\big]\le b(x)\quad\text{and}\quad\mathbb E^Q\big[|b(T_n(x,a,Z_{n+1}))|\big]\le\alpha b(x),$$
--
--   and both integrands are $Q$-integrable.
--
--   These bounds make all the integrals of the operators finite.
--
--   Differences from the source:
--   - reading: Q ∈ 𝒬_n → Q ∈ 𝒬_{n+1}; reason: Assumption 3.1 (i), from which the bounds are derived, is for 𝒬_{n+1}, and Ω_n differs from Ω_{n+1}
--   - generalization: the two inequalities → the two inequalities and integrability of c_n and b ∘ T_n under Q; reason: this only adds clauses; without them a Bochner integral could be a junk 0
--   - encoding: Assumption 3.1: there exist α, ϵ̲, ϵ̄, b̲, b̄, K; expectation inequalities; the closed ball B_ϵ(x̄, ā) → the data B : BoundingData, with the theorem for every such data; lower Lebesgue integrals of the nonnegative parts; a neighbourhood U of (x̄, ā); reason: for all data implies the existence form; the integrals are the same with integrability carried; closed balls of a compatible metric are a neighbourhood base
--   - encoding: T_n and c_n are defined on D_n × Z and D_n × E, with their continuity on those sets → total measurable functions on (E × A) × Z and (E × A) × E, with ContinuousOn and LowerSemicontinuousOn on D_n and D_n × E; reason: D_n is measurable, so every paper model extends by a constant, and only values on D_n enter a statement
--   - encoding: stages n = 0, …, N − 1 and ambiguity sets n = 1, …, N → ℕ-indexed families used at n < N and at 1 ≤ n ≤ N, and Fin N for the rules of a policy; N = 0 is not excluded; reason: the other indices are unused, and N = 0 is a harmless empty case
--   - generalization: under Assumption 3.1, with E and A Borel spaces → under Assumption 3.1 (i) alone, with E and A arbitrary measurable spaces; reason: the remark's bounds follow from part (i) ("the absolute value is the sum of positive and negative part"); the full assumption on Borel spaces is a special case
-- source:
--   Bäuerle & Glauner, arXiv:2007.13103v1, Remark 3.2 (a), p.6

import Mathlib
import Definitions.Def_BorelRobustMDP_Assumption31

open MeasureTheory

namespace BorelRobustMDP

universe u v

/-- Remark 3.2 (a) (Bäuerle & Glauner, arXiv:2007.13103v1, p.6). For `n < N`, `Q ∈ 𝒬_{n+1}` and
`(x, a) ∈ D_n`: `E^Q|c_n(x, a, T_n(x, a, Z_{n+1}))| ≤ b(x)` and `E^Q|b(T_n(x, a, Z_{n+1}))| ≤ α b(x)`.

**Formalization Note.** The printed `Q ∈ 𝒬_n` is read as `Q ∈ 𝒬_{n+1}`, as in Assumption 3.1 (i).
The integrability of both integrands is added, so that the Bochner integrals are the paper's. -/
theorem remark_3_2_a {E A : Type u} {Z : Type v} [MeasurableSpace E] [MeasurableSpace A]
    [MeasurableSpace Z] {N : ℕ} (R : RobustModel E A Z N) (B : BoundingData E)
    (h31 : Assumption31_i R B) (n : ℕ) (hn : n < N) (Q : Measure Z) (hQ : Q ∈ R.𝒬 (n + 1))
    (y : E × A) (hy : y ∈ R.D n) :
    Integrable (fun z => R.c n y (R.T n y z)) Q ∧
      ∫ z, |R.c n y (R.T n y z)| ∂Q ≤ B.b y.1 ∧
      Integrable (fun z => B.b (R.T n y z)) Q ∧
      ∫ z, |B.b (R.T n y z)| ∂Q ≤ B.α * B.b y.1 := by sorry

end BorelRobustMDP
