-- Prove2me | Theorems.Thm_DSICHardRev_theorem_4_5
-- name    : DSICHardRev.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:37:00.657206+00:00
-- url     : https://prove2.me/theorems/2a9d954e-0a5e-408b-bdc3-5d9c31bb2c1b
-- title:
--   Theorem 4.5 — a good DSIC mechanism yields a good simultaneous algorithm on the KSSHD
-- statement:
--   Let $\eta\ge800$ and $\lambda\in[m^{10},2^{m/2}]$. Let $\mathcal H$ be an $(\alpha,\eta,\lambda,C,\mathcal U)$-KSSHD on $m$ regular items, with $\alpha\eta^2\le m$ if $\mathcal H$ uses GS or XOS valuations and $\alpha\eta\le m$ if it uses general valuations. Suppose there is a deterministic, IR, NNT, DSIC mechanism $\mathrm{MECH}'$ for the bidders of $\mathcal H$ on $[m]\cup\{\dagger\}$ which attains an $\eta/800$-approximation using $\lambda/m^9$ communication on $\mathcal V[-2^m,2^m](\mathcal H)$. Then there exists a simultaneous algorithm on $\mathcal H$ which attains an $\eta/40$-approximation using at most $\lambda/m^9$ communication.
--
--   Combined with Theorem 3.7, which requires $\lambda/\eta^2$ bits, this rules out such mechanisms.
--
--   Differences from the source:
--   - encoding: items [m] ∪ {†} → Option (Fin m), none = †; reason: a relabelling
--   - encoding: the n = κη bidders of H → the bidders of H, pairs (k, i); reason: Property (5)
--   - reading: communication of MECH′ ("the worst-case length of the transcript") → maximum over all root-to-leaf paths of ∑_i ⌈log₂ k_i⌉ per node; reason: the literal reading of Definitions 2.4, 2.7 with messages from finite lists
--   - reading: DSIC (Definition 2.11) → prescribed strategy weakly best against every strategy profile of the others, for valuations in the domain; IR and NNT under prescribed play on profiles from the domain; reason: Definitions 2.8, 2.9, 2.11
--   - encoding: an η/800-approximation → OPT ≤ (η/800) · welfare on every profile of the domain; reason: no division by η
--   - reading: all relevant quantities are integers (p.7) → α, η, λ, β = m/η, κ = m/(2α) natural numbers with β·η = m and κ·(2α) = m; reason: the paper's standing integrality convention
--   - encoding: the distribution of Properties (5)–(12) → the uniform law on valid samples (j, ϑ, φ), m ≥ 1, κα + β − α ≤ m; reason: the same law (every choice of A, B admits the same number of bijections); m ≥ 1 excludes the empty auction with no groups, and the size condition is exactly that the sets of Property (7) exist
--   - reading: u_x is either (a) or (b) for each x → one branch (GS, XOS or general) for all x; reason: a KSSHD "using GS valuations" / "for general valuations" is how the paper uses the definition
--   - encoding: a (possibly random) simultaneous algorithm; its communication → bidder messages drawn from distributions depending on (φ_k, x_i), independent across bidders, a randomized referee; communication ∑_i ⌈log₂ K_i⌉ bits; reason: private randomness is the same as such behavioural randomization; the bit cost of fixed-length messages from a list (decision of the plan)
--   - reading: attaining an η/40-approximation on a KSSHD → E_H[OPT] ≤ (η/40) · E_{H, coins}[welfare]; reason: approximation in expectation over the KSSHD, as in the proof of Theorem 3.7 (p.15)
--   - reading: using λ/m⁹ communication → communication ≤ λ/m⁹; reason: "using X communication" bounds the worst-case transcript length (Definition 2.7)
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), §4.3, p.20, Theorem 4.5

import Mathlib
import Definitions.Def_DSICHardRev_Protocol
import Definitions.Def_DSICHardRev_ReductionClass
import Definitions.Def_DSICHardRev_SimAlg

namespace DSICHardRev

/-- **Theorem 4.5** (F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…), §4.3, p.20):
let `η ≥ 800` and `λ ∈ [m^{10}, 2^{m/2}]`. Let `H` be an `(α, η, λ, C, U)`-KSSHD, with `αη² ≤ m` if `H`
uses GS or XOS valuations and `αη ≤ m` if `H` uses general valuations. Suppose there is a
deterministic, IR, NNT, DSIC mechanism `MECH′` which attains an `η/800`-approximation using `λ/m⁹`
communication on `V[−2^m, 2^m](H)`. Then there exists a simultaneous algorithm which attains an
`η/40`-approximation on `H` using `λ/m⁹` communication.

**Formalization Note.** `MECH′` is a mechanism for the bidders of `H` on `[m] ∪ {†}`
(`Option (Fin m)`), deterministic by construction; "using `λ/m⁹` communication" is `comm ≤ λ/m⁹`.
The simultaneous algorithm (`SimAlg H`) is on the bidders and the `m` regular items of `H`, may use
independent private randomness of the bidders and the referee, and attains the approximation in
expectation over `H`. -/
theorem theorem_4_5 {m : ℕ} (H : KSSHD m) (hη : 800 ≤ H.η)
    (hlam₁ : (m : ℝ) ^ 10 ≤ H.lam) (hlam₂ : (H.lam : ℝ) ≤ (2 : ℝ) ^ ((m : ℝ) / 2))
    (hgs : H.branch ≠ .gen → H.α * H.η ^ 2 ≤ m) (hgen : H.branch = .gen → H.α * H.η ≤ m)
    (M' : Mechanism H.Bidder (Option (Fin m)))
    (hIR : M'.IsIR (H.Vrange (-(2 : ℤ) ^ m) ((2 : ℤ) ^ m)))
    (hNNT : M'.IsNNT (H.Vrange (-(2 : ℤ) ^ m) ((2 : ℤ) ^ m)))
    (hDSIC : M'.IsDSIC (H.Vrange (-(2 : ℤ) ^ m) ((2 : ℤ) ^ m)))
    (hApprox : M'.IsApprox (H.Vrange (-(2 : ℤ) ^ m) ((2 : ℤ) ^ m)) ((H.η : ℝ) / 800))
    (hcomm : (M'.comm : ℝ) ≤ (H.lam : ℝ) / (m : ℝ) ^ 9) :
    ∃ A : SimAlg H, A.IsApprox ((H.η : ℝ) / 40) ∧ (A.comm : ℝ) ≤ (H.lam : ℝ) / (m : ℝ) ^ 9 := by sorry

end DSICHardRev
