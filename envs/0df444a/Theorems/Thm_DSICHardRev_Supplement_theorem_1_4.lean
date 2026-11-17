-- Prove2me | Theorems.Thm_DSICHardRev_Supplement_theorem_1_4
-- name    : DSICHardRev.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:11:37.965728+00:00
-- url     : https://prove2.me/theorems/aa66b4db-d154-42d5-bfd9-1b8288016f60
-- title:
--   Theorem 1.4 — simultaneous $(15/16+\varepsilon)$-approximation for two matroid rank valuations needs $2^{\Omega(m)}$ communication
-- statement:
--   Consider two bidders with matroid rank valuations on $m$ items, and (possibly randomized) simultaneous algorithms: each bidder sends one message drawn from a distribution depending only on its own valuation, and a referee chooses a random allocation from the two messages.
--
--   **Theorem.** For every $\varepsilon\in(0,1/16]$ there are $c>0$ and $m_0$ such that for every $m\ge m_0$, every simultaneous algorithm for two bidders on $m$ items with
--   $$
--   \mathbb E\big[v_1(S_1)+v_2(S_2)\big]\;\ge\;\Big(\frac{15}{16}+\varepsilon\Big)\max_{(T_1,T_2)}\big(v_1(T_1)+v_2(T_2)\big)
--   $$
--   for every pair of matroid rank functions $v_1,v_2$ uses at least $2^{cm}$ bits of communication.
--
--   Matroid rank valuations admit exact welfare maximization with interaction; this theorem shows that one round of communication cannot approximate arbitrarily well, and it is the warm-up for the DSIC lower bound of Theorem 1.5.
--
--   **Formalization Note** "Exponential communication" is read as $2^{\Omega(m)}$, with $c$ and $m_0$ allowed to depend on $\varepsilon$ (a constant). The guarantee is worst case over profiles and in expectation over the algorithm's coins. Communication is $\sum_i\lceil\log_2 K_i\rceil$ for alphabets of sizes $K_1,K_2$.
--
--   Differences from the source:
--
--   - reading: uses exponential communication → ∃ c > 0, ∃ m₀, ∀ m ≥ m₀: 2^{c·m} ≤ comm, with c, m₀ depending on ε; reason: standard reading of 'exponential' as 2^{Ω(m)}; the proof gives Ω(λ) with λ = 2^{ε²m} (p.31)
--   - reading: simultaneous algorithm, each bidder sends a (possibly random) message → TwoSimAlg: private-coin message distributions per bidder, independent across bidders, and a randomized referee; reason: the paper's model (p.8, Definition 2.5) with private randomness; no public coin is modelled
--   - encoding: communication = worst-case transcript length → ∑ i, ⌈log₂ K_i⌉ for alphabets Fin K_i; reason: fixed-length encoding of one simultaneous round; the base mission's SimAlg.comm convention
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), Theorem 1.4, p.3 (proof App. A, pp.29–31)

import Mathlib
import Definitions.Def_DSICHardRev_Supplement_Domains
import Definitions.Def_DSICHardRev_Supplement_TwoSimAlg

namespace DSICHardRev

namespace Supplement

/-- **Theorem 1.4** (F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…), §1.2, p.3; proof App. A, pp.29–31):
for every constant `ε ∈ (0, 1/16]`, any simultaneous algorithm attaining a `(15/16 + ε)`-approximation
for two matroid rank valuations uses exponential communication.

**Formalization Note.** "Exponential communication" is read as `2^{Ω(m)}`: for every `ε ∈ (0, 1/16]`
there are `c > 0` and `m₀` (both depending on `ε`) such that for every `m ≥ m₀`, every (possibly
randomized) simultaneous algorithm `A` for two bidders on the items `Fin m` with
`(15/16 + ε) · OPT ≤ E[welfare]` on **every** pair of matroid rank functions on `Fin m` (worst case
over profiles, expectation over the algorithm's coins) has `comm A ≥ 2^{c m}` bits. -/
theorem theorem_1_4 :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 16 →
      ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ A : TwoSimAlg m,
        A.IsApproxRatio (DMR m) (15 / 16 + ε) →
        (2 : ℝ) ^ (c * (m : ℝ)) ≤ (A.comm : ℝ) := by sorry

end Supplement

end DSICHardRev
