-- Prove2me | Theorems.Thm_CoordBoundaries_Throughput_lemma_4_1
-- name    : CoordBoundaries.Throughput.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:49:27.889077+00:00
-- url     : https://prove2.me/theorems/da603649-d39e-4161-82df-67d4ed49cc09
-- title:
--   Lemma 4.1 — stability of the penalized stage LPs and F ≥ (1 − 3η)OPT
-- statement:
--   Fix a candidate $(\mathcal B,\mathcal S,K)$, $\eta=1/q\le1/100$, $\beta=\eta$, $\gamma=\eta/100$ and $\Delta$, and consider the projected procedure of §4.2–§4.3 with any tie-breaking among optimal stage solutions.
--
--   1. Each candidate either becomes infeasible or satisfies the stopping condition $\|y^{i+1}-y^i\|_2^2\le\gamma F_{i+1}$ within $\lfloor 4n/(\beta\gamma)\rfloor+1$ transitions: if stages $0,\dots,\lfloor 4n/(\beta\gamma)\rfloor+1$ are all feasible, the test holds at some transition $i\to i+1$ with $i<\lfloor 4n/(\beta\gamma)\rfloor+1$.
--   2. If the candidate admits a schedule $O'$ satisfying Lemma 2.1 (a)–(d) (the structural case $\mathrm{OPT}\ge H$), then it never becomes infeasible and every stage solution, in particular the terminal one, has
--   $$F\ge(1-3\eta)\mathrm{OPT}.$$
--   Hence selecting the feasible candidate with largest terminal $F$ gives $F\ge(1-3\eta)\mathrm{OPT}$.
--
--   The lemma bounds the number of LP re-solves in the pseudopolynomial implementation and keeps the near-optimal fractional value.
--
--   **Formalization Note** Stage sets are the actual marginal projections of the configuration copies; a run quantifies over every choice of stage maximizers.
--
--   Differences from the source:
--   - reading: "selecting the feasible candidate with largest terminal F gives F ≥ (1 − 3η)OPT" → the certified candidate is never infeasible and all its stage optima have F ≥ (1 − 3η)OPT; reason: the selected maximum is at least the certified candidate’s terminal F
--   - generalization: "In the structural case OPT ≥ H" (the candidate certified by Lemma 2.1) → any candidate admitting a schedule with Lemma 2.1 (a)–(d), for every stage and every run; reason: OPT ≥ H enters only through Lemma 2.1’s O′; the bound at every stage contains the terminal one
--   - generalization: ∆ = 4η^{−4}(⌈log₂(T + 1)⌉ + 1) → any ∆ ∈ ℕ; reason: the proof uses only the density constraints, whatever ∆
--   - encoding: "within ⌊4n/(βγ)⌋ + 1 transitions", "regardless of how ties … are broken" → for every run in which stages 0..M are feasible (M = ⌊4n/(βγ)⌋ + 1) with y^i any maximizer of Φ̂ over P_i, the test holds at some i < M; reason: a run that stops or becomes infeasible earlier satisfies the claim trivially
--   - encoding: stage-i constraints with copies x^[0..i] linked through y → P_i = marginals satisfying the base constraints and admitting one copy with consistent projected distributions per tracked family; reason: copies share only y, so the extension conditions separate
--   - generalization: the residual instance after discarding individually infeasible jobs in §2, with positive machine count and configuration cap → also permits jobs with processing time exceeding their window length, zero machines, a zero configuration cap; reason: individually infeasible jobs occur in no feasible configuration or schedule; the extra zero cases have only empty configurations or zero marginals, and every source instance is included
--   - generalization: tracked histories arising from the preceding stage solutions → nonemptiness for every finite history of job subsets, including subsets that are not valid tracked sets; reason: projecting a single feasible reference schedule onto any job subsets gives disjoint recorded subsets and consistent point-mass distributions
-- source:
--   Tong and Xu, Coordinating Boundaries: Improved Approximation Algorithms for Unweighted Non-Preemptive Throughput Maximization, preprint of October 25, 2026 (STOC 2027 submission #141; source.pdf sha256 59f76539a5ee555f9e56603a067e9f858f38d003011e90b1716085348673687e), p. 23, Lemma 4.1 (setting §4.2–§4.3, pp. 21–23)

import Mathlib
import Definitions.Def_CoordBoundaries_Throughput_StageLP

open Classical

namespace CoordBoundaries.Throughput

/-- **Lemma 4.1** (Tong–Xu, p. 23). For a candidate `(ℬ, 𝒮, K)`, `η = 1/q ≤ 1/100`, `β = η`,
`γ = η/100`, and every run of the penalized stage procedure (any tie-breaking among optimizers):
(1) if stages `0, …, ⌊4n/(βγ)⌋ + 1` are all feasible, then the stopping condition
`‖y^{i+1} − y^i‖₂² ≤ γF_{i+1}` holds at some transition `i → i+1` with `i < ⌊4n/(βγ)⌋ + 1`;
(2) if the candidate admits a reference schedule `O′` with Lemma 2.1 (a)–(d), it never becomes
infeasible and every stage optimum (in particular the terminal one) has `F ≥ (1 − 3η) OPT`, so the
feasible candidate with largest terminal `F` has `F ≥ (1 − 3η) OPT`. -/
theorem lemma_4_1 {I : Instance} (hI : I.Valid) (P : Partition I.T) (K Δ q : ℕ) (hq : 100 ≤ q) :
    (∀ y : ℕ → Marg I P,
      P.IsRun K Δ q y (⌊(4 * I.n : ℝ) / (eta q * gammaP q)⌋₊ + 1) →
      ∃ i < ⌊(4 * I.n : ℝ) / (eta q * gammaP q)⌋₊ + 1,
        P.sqDist (y i) (y (i + 1)) ≤ gammaP q * P.margF (y (i + 1))) ∧
    (∀ O : Sched I, P.Certifies q Δ K O →
      (∀ Hs, (P.StageSet K Δ q Hs).Nonempty) ∧
      ∀ (y : ℕ → Marg I P) (M : ℕ), P.IsRun K Δ q y M → ∀ i ≤ M,
        (1 - 3 * eta q) * (OPT I : ℝ) ≤ P.margF (y i)) := by sorry

end CoordBoundaries.Throughput
