-- Prove2me | Theorems.Thm_DSICHardRev_Supplement_theorem_1_7
-- name    : DSICHardRev.Supplement.theorem_1_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:13:17.640192+00:00
-- url     : https://prove2.me/theorems/96a806ca-4339-426b-b220-6681cd0024fc
-- title:
--   Theorem 1.7 — an IR, NNT, universally DSIC $(\sqrt5-1)/2\approx0.618$-approximation for two submodular valuations with polynomial communication
-- statement:
--   Consider two bidders with monotone submodular valuations on $m$ items with values in the range $R$ of p.8, and randomized mechanisms given as probability distributions over deterministic mechanisms.
--
--   **Theorem.** There are constants $C$ and $k$ such that for every $m\ge1$ there is a distribution $\mu$ over deterministic mechanisms for two bidders on $m$ items such that
--   1. every mechanism in the support of $\mu$ is individually rational, has no negative transfers, is dominant-strategy incentive compatible on $\mathcal D_{\mathrm{SUB}}(m)$, and uses at most $C\,m^k$ bits;
--   2. on every profile from $\mathcal D_{\mathrm{SUB}}(m)$,
--   $$
--   \mathbb E_\mu\big[v_1(S_1)+v_2(S_2)\big]\;\ge\;\frac{\sqrt5-1}{2}\,\max_{(T_1,T_2)}\big(v_1(T_1)+v_2(T_2)\big).
--   $$
--
--   This is the first polynomial-communication truthful mechanism to beat $1/2$ for two submodular valuations, and the first polynomial-communication DSIC mechanism to beat $1/2$ for two weighted matroid rank valuations.
--
--   **Formalization Note** "Polynomial communication" is read as every support mechanism using at most $C m^k$ bits, $C,k$ independent of $m$. The constant is the exact inverse golden ratio.
--
--   Differences from the source:
--
--   - reading: using polynomial communication → ∃ C : ℝ, ∃ k : ℕ, ∀ m ≥ 1: every mechanism in the support has comm ≤ C · m^k; reason: standard reading with C and k uniform in m; the communication of a randomized mechanism is the worst case over its randomness
--   - encoding: IR, NNT, universally DSIC mechanism → a PMF μ over deterministic Mechanism (Fin 2) (Fin m) whose every support element is IR, NNT and DSIC on DSUB m; reason: Definition 2.12 with μ as the witness; IR and NNT hold on every outcome (p.9)
--   - encoding: submodular valuations 2^M → ℝ+ → monotone submodular valuations on Fin m with every value in Rset m; reason: the paper's global conventions: monotone (p.9) and values in R (p.8)
--   - encoding: E[welfare] ≥ ((√5−1)/2) · max_T welfare → ((√5 − 1)/2) · welfare v T ≤ expWelfare μ v for every disjoint T; reason: no maximum or division; same instances
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), Theorem 1.7, p.4 (proof App. D, pp.42–44)

import Mathlib
import Definitions.Def_DSICHardRev_Protocol
import Definitions.Def_DSICHardRev_Supplement_Domains
import Definitions.Def_DSICHardRev_Supplement_RandMechanism

namespace DSICHardRev

namespace Supplement

/-- **Theorem 1.7** (F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…), §1.2, p.4; proof App. D, pp.42–44):
there exists a `(√5 − 1)/2 ≈ 0.618`-approximation for two submodular valuations with an IR, NNT,
universally DSIC mechanism using polynomial communication.

**Formalization Note.** "Polynomial communication" is read as: there are constants `C` and `k`,
independent of `m`, such that for every `m ≥ 1` there is a distribution `μ` over deterministic
mechanisms for two bidders on the items `Fin m` whose every support mechanism is IR, NNT and DSIC
(against all strategy profiles) on `DSUB m` (monotone submodular valuations with values in the range
`R` of p.8) and uses at most `C · m^k` bits, with `((√5 − 1)/2) · OPT ≤ E[welfare]` on every profile
from `DSUB m`. The ratio is the exact constant `(√5 − 1)/2`. -/
theorem theorem_1_7 :
    ∃ C : ℝ, ∃ k : ℕ, ∀ m : ℕ, 1 ≤ m → ∃ μ : RandMechanism (Fin 2) (Fin m),
      RandMechanism.IsIRNNTUnivDSIC μ (DSUB m) ∧
      (∀ M ∈ PMF.support μ, (M.comm : ℝ) ≤ C * (m : ℝ) ^ k) ∧
      RandMechanism.IsApproxRatio μ (DSUB m) ((Real.sqrt 5 - 1) / 2) := by sorry

end Supplement

end DSICHardRev
