-- Prove2me | Theorems.Thm_DSICHardRev_proposition_4_1
-- name    : DSICHardRev.proposition_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:36:34.308224+00:00
-- url     : https://prove2.me/theorems/8582a7f0-3467-4553-bd8a-1234c3aa67de
-- title:
--   Proposition 4.1 — good DSIC mechanisms make almost every bidder signal in the first round
-- statement:
--   Let $\eta\ge800$ and $\alpha\eta\le m$, and let $\mathcal H$ be an $(\alpha,\eta,\lambda,C,\mathcal U)$-KSSHD using GS, XOS or general valuations. Suppose $\mathrm{MECH}'$ is a deterministic, IR, NNT, DSIC mechanism which attains an $\eta/800$-approximation using $\Gamma\le2^{m/2}$ communication on $\mathcal V[-2^m,2^m](\mathcal H)$. Then there exists a mechanism $\mathrm{MECH}$ such that
--
--   1. $\mathrm{MECH}$ is a deterministic, IR, NNT, DSIC mechanism which attains an $\eta/800$-approximation using $\Gamma$ communication on $\mathcal V[-m,m](\mathcal H)$;
--   2. letting $\xi_i(v)$ be the first-round message $\mathrm{MECH}$ prescribes to bidder $i$ with valuation $v$, there is a bidder $i^\dagger$ such that for all $i\neq i^\dagger$ and $v\in\mathcal V(\mathcal H)$ there is $t\in\{1,\dots,m^4\}$ with
--   $$\xi_i(v_{0,0})=\xi_i(v_{0,t-1})\neq\xi_i(v_{0,t}).$$
--
--   This is the commitment property that lets a simultaneous algorithm read the special bidders from first messages (Theorem 4.5).
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
--   - encoding: t ∈ [m⁴] → t : ℕ with 1 ≤ t ≤ m⁴; reason: [m⁴] = {1, …, m⁴}
--   - reading: using Γ communication → communication ≤ Γ; reason: "using X communication" bounds the worst-case transcript length (Definition 2.7)
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), §4.2, p.17, Proposition 4.1

import Mathlib
import Definitions.Def_DSICHardRev_Protocol
import Definitions.Def_DSICHardRev_ReductionClass

namespace DSICHardRev

/-- **Proposition 4.1** (F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…), §4.2, p.17):
let `η ≥ 800` and `αη ≤ m`, and let `H` be an `(α, η, λ, C, U)`-KSSHD using GS, XOS or general
valuations. Suppose `MECH′` is a deterministic, IR, NNT, DSIC mechanism which attains an
`η/800`-approximation using `Γ ≤ 2^{m/2}` communication on `V[−2^m, 2^m](H)`. Then there exists a
mechanism `MECH` such that (1) `MECH` is a deterministic, IR, NNT, DSIC mechanism which attains an
`η/800`-approximation using `Γ` communication on `V[−m, m](H)`; (2) with `ξ_i(v)` the message
`MECH` prescribes bidder `i` to send (in the first round) when its valuation is `v`, there is a bidder
`i†` such that for all `i ≠ i†` and `v ∈ V(H)` there is `t ∈ [m⁴]` with
`ξ_i(v_{0,0}) = ξ_i(v_{0,t−1}) ≠ ξ_i(v_{0,t})`.

**Formalization Note.** The hypotheses are those of Proposition 4.1: \`η ≥ 800\`, \`αη ≤ m\`, \`H\`
any KSSHD (GS, XOS or general), \`MECH′\` a mechanism for the bidders of \`H\` on the items
\`[m] ∪ {†}\` (\`Option (Fin m)\`, \`none = †\`), deterministic by construction, IR, NNT, DSIC and
attaining an \`η/800\`-approximation on \`V[−2^m, 2^m](H)\`, with communication \`≤ Γ ≤ 2^{m/2}\`. `[m⁴] = {1, …, m⁴}`. `ξ_i` is `rootMsg` (`none` if the root is a leaf). `v_{s,t}`
is `vst0` (for general valuations `v_{s,t,M,M}`). -/
theorem proposition_4_1 {m : ℕ} (H : KSSHD m) (hη : 800 ≤ H.η) (hαη : H.α * H.η ≤ m)
    (M' : Mechanism H.Bidder (Option (Fin m))) (Γ : ℝ)
    (hIR : M'.IsIR (H.Vrange (-(2 : ℤ) ^ m) ((2 : ℤ) ^ m)))
    (hNNT : M'.IsNNT (H.Vrange (-(2 : ℤ) ^ m) ((2 : ℤ) ^ m)))
    (hDSIC : M'.IsDSIC (H.Vrange (-(2 : ℤ) ^ m) ((2 : ℤ) ^ m)))
    (hApprox : M'.IsApprox (H.Vrange (-(2 : ℤ) ^ m) ((2 : ℤ) ^ m)) ((H.η : ℝ) / 800))
    (hcomm : (M'.comm : ℝ) ≤ Γ) (hΓ : Γ ≤ (2 : ℝ) ^ ((m : ℝ) / 2)) :
    ∃ M : Mechanism H.Bidder (Option (Fin m)),
      (M.IsIR (H.Vrange (-(m : ℤ)) m) ∧ M.IsNNT (H.Vrange (-(m : ℤ)) m) ∧
        M.IsDSIC (H.Vrange (-(m : ℤ)) m) ∧
        M.IsApprox (H.Vrange (-(m : ℤ)) m) ((H.η : ℝ) / 800) ∧ (M.comm : ℝ) ≤ Γ) ∧
      ∃ i₀ : H.Bidder, ∀ i, i ≠ i₀ → ∀ v ∈ H.VH, ∃ t : ℕ, 1 ≤ t ∧ t ≤ m ^ 4 ∧
        Protocol.rootMsg M.protocol (M.prescribe i (H.vst0 v 0 0)) =
          Protocol.rootMsg M.protocol (M.prescribe i (H.vst0 v 0 ((t : ℝ) - 1))) ∧
        Protocol.rootMsg M.protocol (M.prescribe i (H.vst0 v 0 ((t : ℝ) - 1))) ≠
          Protocol.rootMsg M.protocol (M.prescribe i (H.vst0 v 0 t)) := by sorry

end DSICHardRev
