-- Prove2me | Theorems.Thm_CompNonlocal_Supplement_theorem_8_commitments_from_certification
-- name    : CompNonlocal.Supplement.theorem_8_commitments_from_certification
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:12:44.223252+00:00
-- url     : https://prove2.me/theorems/3117d8b9-dd9e-4686-a95c-11c4678a4f04
-- title:
--   Theorem 8 — near-optimal certification of $\rho(v)$ gives statistically sum-binding QCCC commitments
-- statement:
--   Let $v\in(1/3,1]$ and suppose the Werner state $\rho(v)$ is $\gamma$-single-copy certifiable (Definition 11) with
--   $$\gamma\ \ge\ (1-2^{-24})\,\frac{v-1/3}{2}.$$
--   Then there exists a QCCC bit commitment scheme that is correct, computationally hiding against honest-but-curious receivers, and statistically sum-binding against computationally unbounded quantum committers (Definition 6).
--
--   The hypothesis is the one of the mission's goal (Theorem 1); Theorem 8 adds commitments to its consequences.
--
--   Differences from the source:
--   - encoding: QCCC commit protocol with polynomially many rounds, each party a QPT algorithm keeping quantum memory → each party runs one uniform Clifford+T circuit family in all its rounds with the round number as classical input; committer in even rounds, receiver in odd rounds; messages of fixed length per κ; number of rounds polynomially bounded and polynomial-time computable; reason: a uniform sequence of round circuits merges into one uniform circuit branching on the round number, and empty messages give any speaking order, so the protocols are the same up to polynomial overhead
--   - encoding: unbounded committer A* with arbitrary private quantum memory; unbounded openers O*_0, O*_1 → committer: arbitrary finite memory, arbitrary initial state, Kraus instruments per round with outcome the message; openers: per-transcript POVMs on the committer's memory with outcomes in {0,1}^L, any L; the committer's messages are N-bit strings, N the honest committer's message length; reason: these are all quantum strategies; processing between messages is absorbed into the next instrument or the opener, Ver reads a finite prefix of d, and the protocol's message space in the committer's rounds is {0,1}^N
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7b7dd5f4c52119a37e0ee1d00eaf20185262775b8ab7d3067a9f2fcae), Theorem 8, p.53 (proof §10, pp.53–63)

import Mathlib
import Definitions.Def_CompNonlocal_IsSingleCopyCertifiable
import Definitions.Def_CompNonlocal_werner
import Definitions.Def_CompNonlocal_Supplement_IsHBCCommitment

set_option autoImplicit false

namespace CompNonlocal.Supplement

open CompNonlocal

/-- Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), Theorem 8, p.53: "Theorem 8 (Commitments from certification). Let v ∈ (1/3, 1] be fixed
and suppose ρ(v) is γ-single-copy certifiable with γ ≥ (1 − 2^{−24}) (v − 1/3)/2. Then there exists a
statistically sum-binding QCCC commitment with computational HBC hiding (Definition 6)."

The hypothesis is the one of the mission's goal (the published `IsSingleCopyCertifiable` of the
Werner state `werner v`, Definition 11); the conclusion is a commitment scheme satisfying
`IsHBCCommitment` (Definition 6: correctness, computational HBC hiding against polynomial-size
distinguishers with advice reading the receiver's full view, statistical sum binding against
unbounded committers and openers with one negligible `ϵ_bind`).

**Formalization Note** The commitment is a multi-round QCCC protocol (`Commitment`): honest parties
are uniform Clifford+T circuit families that keep quantum memory between rounds and exchange only
classical messages. -/
theorem theorem_8_commitments_from_certification (v : ℝ) (hv₁ : 1 / 3 < v) (hv₂ : v ≤ 1)
    (γ : ℝ) (hγ : (1 - (2 : ℝ) ^ (-24 : ℤ)) * ((v - 1 / 3) / 2) ≤ γ)
    (h : IsSingleCopyCertifiable (werner v) γ) :
    ∃ P : Commitment, IsHBCCommitment P := by sorry

end CompNonlocal.Supplement
