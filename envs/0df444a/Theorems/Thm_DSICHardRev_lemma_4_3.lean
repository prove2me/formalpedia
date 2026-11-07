-- Prove2me | Theorems.Thm_DSICHardRev_lemma_4_3
-- name    : DSICHardRev.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:36:38.362854+00:00
-- url     : https://prove2.me/theorems/6cd92b2c-bb3b-4c60-b156-9f6628addfd8
-- title:
--   Lemma 4.3 — a mechanism whose first round is informative at the default scale
-- statement:
--   Under the hypotheses of Proposition 4.1 ($\eta\ge800$, $\alpha\eta\le m$, $\mathrm{MECH}'$ deterministic, IR, NNT, DSIC, $\eta/800$-approximate with $\Gamma\le2^{m/2}$ communication on $\mathcal V[-2^m,2^m](\mathcal H)$), there exists a deterministic, IR, NNT, DSIC mechanism $\mathrm{MECH}$ that attains an $\eta/800$-approximation using $\Gamma$ communication on $\mathcal V[-m,m](\mathcal H)$, together with a bidder $i^\dagger$ and $u,u'\in\mathcal V[-m,m](\mathcal H)$ such that
--
--   1. in the first round the messages prescribed to $i^\dagger$ for $u$ and $u'$ are different;
--   2. $u(\{\dagger\}),u'(\{\dagger\})\in[\alpha\eta^2,2\alpha\eta^2]$ if the valuations are GS or XOS, and $u(M),u'(M)\in[\alpha\eta^2,2\alpha\eta^2]$ if they are general.
--
--   Clause 1 forces the root of $\mathrm{MECH}$ to be an internal node.
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
--   - reading: the message sent in the first round (ξ_i(v), "the first round of communication") → the message at the root of MECH's protocol (rootMsg, which is none when the root is a leaf); reason: the first round is the root node (MECH's tree is rooted at N†, proof of Lemma 4.3, p.19); a leaf sends no message, so a clause asserting two different messages forces the root to be internal
--   - reading: using Γ communication → communication ≤ Γ; reason: "using X communication" bounds the worst-case transcript length (Definition 2.7)
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), §4.2, p.18, Lemma 4.3 (inside the proof of Proposition 4.1, with its hypotheses)

import Mathlib
import Definitions.Def_DSICHardRev_Protocol
import Definitions.Def_DSICHardRev_ReductionClass

namespace DSICHardRev

/-- **Lemma 4.3** (F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…), §4.2, p.18), inside the proof of Proposition 4.1:
there exists a deterministic, IR, NNT, DSIC mechanism `MECH` which attains an `η/800`-approximation
using `Γ` communication on `V[−m, m](H)`. This mechanism has a bidder `i†` and `u, u′ ∈ V[−m, m](H)`
such that (1) in the first round of communication the messages prescribed to `i†` for `u, u′` differ;
(2) `u({†}), u′({†}) ∈ [αη², 2αη²]` (GS or XOS), or `u(M), u′(M) ∈ [αη², 2αη²]` (general).

**Formalization Note.** The hypotheses are those of Proposition 4.1: \`η ≥ 800\`, \`αη ≤ m\`, \`H\`
any KSSHD (GS, XOS or general), \`MECH′\` a mechanism for the bidders of \`H\` on the items
\`[m] ∪ {†}\` (\`Option (Fin m)\`, \`none = †\`), deterministic by construction, IR, NNT, DSIC and
attaining an \`η/800\`-approximation on \`V[−2^m, 2^m](H)\`, with communication \`≤ Γ ≤ 2^{m/2}\`. "Using `Γ` communication" is `comm ≤ Γ`. The first-round message is `rootMsg` (`none`
if the root is a leaf, so clause (1) forces the root to be a node). -/
theorem lemma_4_3 {m : ℕ} (H : KSSHD m) (hη : 800 ≤ H.η) (hαη : H.α * H.η ≤ m)
    (M' : Mechanism H.Bidder (Option (Fin m))) (Γ : ℝ)
    (hIR : M'.IsIR (H.Vrange (-(2 : ℤ) ^ m) ((2 : ℤ) ^ m)))
    (hNNT : M'.IsNNT (H.Vrange (-(2 : ℤ) ^ m) ((2 : ℤ) ^ m)))
    (hDSIC : M'.IsDSIC (H.Vrange (-(2 : ℤ) ^ m) ((2 : ℤ) ^ m)))
    (hApprox : M'.IsApprox (H.Vrange (-(2 : ℤ) ^ m) ((2 : ℤ) ^ m)) ((H.η : ℝ) / 800))
    (hcomm : (M'.comm : ℝ) ≤ Γ) (hΓ : Γ ≤ (2 : ℝ) ^ ((m : ℝ) / 2)) :
    ∃ M : Mechanism H.Bidder (Option (Fin m)),
      M.IsIR (H.Vrange (-(m : ℤ)) m) ∧ M.IsNNT (H.Vrange (-(m : ℤ)) m) ∧
      M.IsDSIC (H.Vrange (-(m : ℤ)) m) ∧ M.IsApprox (H.Vrange (-(m : ℤ)) m) ((H.η : ℝ) / 800) ∧
      (M.comm : ℝ) ≤ Γ ∧
      ∃ (i₀ : H.Bidder) (u u' : Finset (Option (Fin m)) → ℝ),
        u ∈ H.Vrange (-(m : ℤ)) m ∧ u' ∈ H.Vrange (-(m : ℤ)) m ∧
        Protocol.rootMsg M.protocol (M.prescribe i₀ u) ≠
          Protocol.rootMsg M.protocol (M.prescribe i₀ u') ∧
        (H.branch ≠ .gen →
          u {none} ∈ Set.Icc ((H.α : ℝ) * (H.η : ℝ) ^ 2) (2 * (H.α : ℝ) * (H.η : ℝ) ^ 2) ∧
          u' {none} ∈ Set.Icc ((H.α : ℝ) * (H.η : ℝ) ^ 2) (2 * (H.α : ℝ) * (H.η : ℝ) ^ 2)) ∧
        (H.branch = .gen →
          u Finset.univ ∈ Set.Icc ((H.α : ℝ) * (H.η : ℝ) ^ 2) (2 * (H.α : ℝ) * (H.η : ℝ) ^ 2) ∧
          u' Finset.univ ∈ Set.Icc ((H.α : ℝ) * (H.η : ℝ) ^ 2) (2 * (H.α : ℝ) * (H.η : ℝ) ^ 2)) := by sorry

end DSICHardRev
