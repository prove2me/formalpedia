-- Prove2me | Theorems.Thm_DSICHardRev_theorem_3_7
-- name    : DSICHardRev.theorem_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:37:00.978764+00:00
-- url     : https://prove2.me/theorems/b17edcc7-97dc-4e9a-a027-cb6c0a36112b
-- title:
--   Theorem 3.7 — simultaneous $\eta/40$-approximations on a KSSHD need $\lambda/\eta^2$ communication
-- statement:
--   Let $\mathcal H$ be an $(\alpha,\eta,\lambda,C,\mathcal U)$-KSSHD on $m$ items, using GS, XOS or general valuations. Every simultaneous algorithm on $\mathcal H$ that attains an $\eta/40$-approximation uses at least
--   $$\frac{\lambda}{\eta^2}$$
--   bits of communication.
--
--   Together with Theorem 4.5 it shows that a good DSIC mechanism would give a simultaneous algorithm that is too good to exist.
--
--   Differences from the source:
--   - encoding: a (possibly random) simultaneous algorithm; its communication → bidder messages drawn from distributions depending on (φ_k, x_i), independent across bidders, a randomized referee; communication ∑_i ⌈log₂ K_i⌉ bits; reason: private randomness is the same as such behavioural randomization; the bit cost of fixed-length messages from a list (decision of the plan)
--   - reading: attaining an η/40-approximation on a KSSHD → E_H[OPT] ≤ (η/40) · E_{H, coins}[welfare]; reason: approximation in expectation over the KSSHD, as in the proof of Theorem 3.7 (p.15)
--   - reading: all relevant quantities are integers (p.7) → α, η, λ, β = m/η, κ = m/(2α) natural numbers with β·η = m and κ·(2α) = m; reason: the paper's standing integrality convention
--   - encoding: the distribution of Properties (5)–(12) → the uniform law on valid samples (j, ϑ, φ), m ≥ 1, κα + β − α ≤ m; reason: the same law (every choice of A, B admits the same number of bijections); m ≥ 1 excludes the empty auction with no groups, and the size condition is exactly that the sets of Property (7) exist
--   - reading: u_x is either (a) or (b) for each x → one branch (GS, XOS or general) for all x; reason: a KSSHD "using GS valuations" / "for general valuations" is how the paper uses the definition
--   - reading: GS valuations (not defined in the paper) → Kelso–Crawford gross substitutes at all real price vectors (published GrossSubstitutesOn v Set.univ); reason: the standard definition; requiring all real prices is the more restrictive class
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), §3.2, p.15, Theorem 3.7

import Mathlib
import Definitions.Def_DSICHardRev_SimAlg

namespace DSICHardRev

/-- **Theorem 3.7** (F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…), §3.2, p.15):
any simultaneous algorithm attaining an `η/40`-approximation on an `(α, η, λ, C, U)`-KSSHD uses at
least `λ/η²` communication.

**Formalization Note.** Every branch of Definition 3.1 (GS, XOS, general). The algorithm may be
randomized (independent private randomness of the bidders and of the referee); the approximation is
in expectation over the KSSHD and the randomness, `E_H[OPT] ≤ (η/40) E[welfare]`; communication is
`∑_b ⌈log₂ K_b⌉` bits. -/
theorem theorem_3_7 {m : ℕ} (H : KSSHD m) (A : SimAlg H) (hA : A.IsApprox ((H.η : ℝ) / 40)) :
    (H.lam : ℝ) / (H.η : ℝ) ^ 2 ≤ A.comm := by sorry

end DSICHardRev
