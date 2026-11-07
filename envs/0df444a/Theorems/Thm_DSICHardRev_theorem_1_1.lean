-- Prove2me | Theorems.Thm_DSICHardRev_theorem_1_1
-- name    : DSICHardRev.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:35:51.482355+00:00
-- url     : https://prove2.me/theorems/3c4b3280-3912-41ac-8b32-b420d0e275b1
-- title:
--   Theorem 1.1 — deterministic IR, NNT, DSIC mechanisms for GS valuations with $2^\gamma$ communication have approximation ratio $\Omega((m/\gamma)^{1/7})$
-- statement:
--   Let $\mathrm{DSIC}_{GS}(m,\gamma)$ be the optimal approximation ratio attainable on $m$ items with $2^\gamma$ bits of communication by a deterministic, individually rational, no-negative-transfers, dominant-strategy incentive-compatible mechanism for gross-substitutes valuations. Then for $\gamma\in[\log m,\,m]$,
--   $$\mathrm{DSIC}_{GS}(m,\gamma)=\Omega\big((m/\gamma)^{1/7}\big).$$
--
--   Explicitly: there is a constant $c>0$ such that for every $m\ge2$ and every real $\gamma$ with $\log_2m\le\gamma\le m$ there is a number of bidders $n$ for which every deterministic mechanism for $n$ bidders on $m$ items that is IR, NNT and DSIC on the monotone GS valuations with values in the range $R$, uses at most $2^\gamma$ bits of communication and attains an $\eta$-approximation there, satisfies
--   $$\eta\;\ge\;c\,(m/\gamma)^{1/7}.$$
--
--   Since VCG maximizes welfare truthfully for GS valuations with polynomial communication, this separates DSIC from truthfulness on a canonical valuation class and answers the open question of Dobzinski, Ron and Vondrák (2022).
--
--   **Formalization Note** The valuation domain is $\mathcal D_{GS}(m)$ (monotone, $R$-valued, Kelso–Crawford GS). Communication is counted in bits over the whole protocol tree.
--
--   Differences from the source:
--   - reading: 2^γ communication, "the worst-case length of the transcript of the communication protocol" with messages from lists → fixed alphabets per node and bidder, a node costs ∑_i ⌈log₂ k_i⌉ bits, communication = maximum over all root-to-leaf paths of the tree; reason: the literal reading of Definitions 2.4 and 2.7; a protocol whose messages are variable-length strings of worst-case transcript Γ becomes one of cost at most 2Γ + O(1), so the Ω statement is the same under either reading
--   - reading: IR, NNT, DSIC (Definitions 2.8, 2.9, 2.11) → IR and NNT under prescribed play on every profile from the domain; DSIC against every strategy profile of the other bidders, for every valuation in the domain; reason: the definitions as printed; DSIC is not ex-post Nash (Definition 2.10)
--   - reading: DSIC_GS(m, γ), the number of bidders unspecified → ∃ n such that every mechanism for n bidders fails; reason: the optimal ratio over all numbers of bidders; for a fixed small n (e.g. n = 1) the ratio is 1, and the paper's proof uses n = κη
--   - encoding: DSIC_GS(m, γ) = Ω((m/γ)^{1/7}) for γ ∈ [log m, m] → ∃ c > 0, ∀ m ≥ 2, ∀ real γ ∈ [log₂ m, m], every admissible mechanism has η ≥ c (m/γ)^{1/7}; reason: equivalent to the ∃ c, m₀ form since η ≥ 1 for every mechanism on the domain; m ≥ 2 because at m = 1 the range of γ includes 0, where m/γ is undefined
--   - encoding: an η-approximation, E[∑ v_i(S_i)] ≥ (1/η) max ∑ v_i(T_i) → ∑ v_i(T_i) ≤ η · ∑ v_i(S_i) for every allocation T and every profile of the domain; reason: deterministic mechanisms; no division by η
--   - reading: GS valuations (not defined in the paper) → Kelso–Crawford gross substitutes at all real price vectors (published GrossSubstitutesOn v Set.univ); reason: the standard definition; requiring all real prices is the more restrictive class; the lower bound over the smaller class is the stronger theorem
--   - encoding: valuations with values in R (p.8), monotone (p.9) → the domain DGS m: monotone, every value in R, GS; reason: as printed; v(∅) = 0 not required
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), §1.2, p.3, Theorem 1.1 (definition of DSIC_GS(m, γ) and footnote 1)

import Mathlib
import Definitions.Def_DSICHardRev_Protocol
import Definitions.Def_DSICHardRev_GSDomain

namespace DSICHardRev

/-- **Theorem 1.1** (F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…), §1.2, p.3):
`DSIC_GS(m, γ) = Ω((m/γ)^{1/7})` for `γ ∈ [log m, m]`, where `DSIC_GS(m, γ)` is the optimal
approximation ratio attainable on `m` items with `2^γ` communication by a deterministic, IR, NNT,
DSIC mechanism for GS valuations.

**Formalization Note.** `Ω` is read as: there is a constant `c > 0` such that for every `m ≥ 2`
and every real `γ` with `log₂ m ≤ γ ≤ m` there is a number of bidders `n` for which every
deterministic mechanism (`Mechanism`, deterministic by construction) for `n` bidders on the items
`Fin m` that is IR, NNT and DSIC on the domain `DGS m` (monotone GS valuations with values in the
range `R` of p.8), uses at most `2^γ` bits (worst case over the whole protocol tree) and attains an
`η`-approximation on `DGS m` (`OPT ≤ η · welfare` on every profile) has `η ≥ c (m/γ)^{1/7}`. -/
theorem theorem_1_1 :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 2 ≤ m → ∀ γ : ℝ, Real.logb 2 m ≤ γ → γ ≤ m →
      ∃ n : ℕ, 0 < n ∧ ∀ (M : Mechanism (Fin n) (Fin m)) (η : ℝ),
        M.IsIR (DGS m) → M.IsNNT (DGS m) → M.IsDSIC (DGS m) →
        (M.comm : ℝ) ≤ (2 : ℝ) ^ γ → M.IsApprox (DGS m) η →
        c * ((m : ℝ) / γ) ^ ((1 : ℝ) / 7) ≤ η := by sorry

end DSICHardRev
