-- Prove2me | Theorems.Thm_DSICHardRev_lemma_4_4
-- name    : DSICHardRev.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:36:38.748203+00:00
-- url     : https://prove2.me/theorems/4d2a7cba-537d-4dc3-8f25-4a0dff1bccce
-- title:
--   Lemma 4.4 — every other bidder's first message separates $v_{0,0}$ from $v_{0,m\alpha\eta^3}$
-- statement:
--   Let $\eta\ge800$ and $\alpha\eta\le m$, let $\mathcal H$ be an $(\alpha,\eta,\lambda,C,\mathcal U)$-KSSHD using GS, XOS or general valuations, and let $\mathrm{MECH}$ be a deterministic, IR, NNT, DSIC mechanism for the bidders of $\mathcal H$ on $[m]\cup\{\dagger\}$ that attains an $\eta/800$-approximation on $\mathcal V[-m,m](\mathcal H)$. Let $i^\dagger$ and $u,u'\in\mathcal V[-m,m](\mathcal H)$ satisfy the two clauses of Lemma 4.3: the first-round messages of $i^\dagger$ for $u$ and $u'$ differ, and $u(\{\dagger\}),u'(\{\dagger\})\in[\alpha\eta^2,2\alpha\eta^2]$ (GS or XOS), resp. $u(M),u'(M)\in[\alpha\eta^2,2\alpha\eta^2]$ (general). Then for every bidder $i\neq i^\dagger$ and every $v\in\mathcal V(\mathcal H)$,
--   $$\xi_i(v_{0,0})\neq\xi_i(v_{0,m\alpha\eta^3}),$$
--   where $\xi_i$ is the first-round message prescribed by $\mathrm{MECH}$ (for general valuations $v_{s,t}=v_{s,t,M,M}$).
--
--   DSIC forces every bidder other than $i^\dagger$ to reveal something about its value for the special outcome already in the first round.
--
--   Differences from the source:
--   - generalization: the mechanism, bidder and valuations promised by Lemma 4.3 → any mechanism, bidder and valuations with the properties Lemma 4.3 promises (communication not assumed); reason: a weaker hypothesis: the mechanism of Lemma 4.3 has all these properties (and also communication ≤ Γ, which the proof does not use), so the statement specializes to the paper's
--   - encoding: items [m] ∪ {†} → Option (Fin m), none = †; reason: a relabelling
--   - encoding: the n = κη bidders of H → the bidders of H, pairs (k, i); reason: Property (5)
--   - reading: communication of MECH′ ("the worst-case length of the transcript") → maximum over all root-to-leaf paths of ∑_i ⌈log₂ k_i⌉ per node; reason: the literal reading of Definitions 2.4, 2.7 with messages from finite lists
--   - reading: DSIC (Definition 2.11) → prescribed strategy weakly best against every strategy profile of the others, for valuations in the domain; IR and NNT under prescribed play on profiles from the domain; reason: Definitions 2.8, 2.9, 2.11
--   - encoding: an η/800-approximation → OPT ≤ (η/800) · welfare on every profile of the domain; reason: no division by η
--   - reading: all relevant quantities are integers (p.7) → α, η, λ, β = m/η, κ = m/(2α) natural numbers with β·η = m and κ·(2α) = m; reason: the paper's standing integrality convention
--   - encoding: the distribution of Properties (5)–(12) → the uniform law on valid samples (j, ϑ, φ), m ≥ 1, κα + β − α ≤ m; reason: the same law (every choice of A, B admits the same number of bijections); m ≥ 1 excludes the empty auction with no groups, and the size condition is exactly that the sets of Property (7) exist
--   - reading: u_x is either (a) or (b) for each x → one branch (GS, XOS or general) for all x; reason: a KSSHD "using GS valuations" / "for general valuations" is how the paper uses the definition
--   - reading: the message sent in the first round (ξ_i(v), "the first round of communication") → the message at the root of MECH's protocol (rootMsg, which is none when the root is a leaf); reason: the first round is the root node (MECH's tree is rooted at N†, proof of Lemma 4.3, p.19); a leaf sends no message, so a clause asserting two different messages forces the root to be internal
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), §4.2, p.19, Lemma 4.4

import Mathlib
import Definitions.Def_DSICHardRev_Protocol
import Definitions.Def_DSICHardRev_ReductionClass

namespace DSICHardRev

/-- **Lemma 4.4** (F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…), §4.2, p.19), for the mechanism `MECH`, bidder `i†` and valuations
`u, u′ ∈ V[−m, m](H)` promised by Lemma 4.3: for all bidders `i ≠ i†` and all valuations `v ∈ V(H)`,
`ξ_i(v_{0,0}) ≠ ξ_i(v_{0,mαη³})`, where `ξ_i` is the first-round message prescribed by `MECH`.

**Formalization Note.** Stated self-contained: `η ≥ 800`, `αη ≤ m`, `H` any KSSHD, `MECH` a
(deterministic) mechanism for the bidders of `H` on `[m] ∪ {†}` that is IR, NNT, DSIC and attains an
`η/800`-approximation on `V[−m, m](H)`, and `i†, u, u′` satisfying clauses (1)–(2) of Lemma 4.3.
Communication is not used. `v_{s,t}` is `vst0` (for general valuations `v_{s,t,M,M}`, p.19). -/
theorem lemma_4_4 {m : ℕ} (H : KSSHD m) (hη : 800 ≤ H.η) (hαη : H.α * H.η ≤ m)
    (M : Mechanism H.Bidder (Option (Fin m)))
    (hIR : M.IsIR (H.Vrange (-(m : ℤ)) m)) (hNNT : M.IsNNT (H.Vrange (-(m : ℤ)) m))
    (hDSIC : M.IsDSIC (H.Vrange (-(m : ℤ)) m))
    (hApprox : M.IsApprox (H.Vrange (-(m : ℤ)) m) ((H.η : ℝ) / 800))
    (i₀ : H.Bidder) (u u' : Finset (Option (Fin m)) → ℝ)
    (hu : u ∈ H.Vrange (-(m : ℤ)) m) (hu' : u' ∈ H.Vrange (-(m : ℤ)) m)
    (h₁ : Protocol.rootMsg M.protocol (M.prescribe i₀ u) ≠
      Protocol.rootMsg M.protocol (M.prescribe i₀ u'))
    (h₂ : H.branch ≠ .gen →
      u {none} ∈ Set.Icc ((H.α : ℝ) * (H.η : ℝ) ^ 2) (2 * (H.α : ℝ) * (H.η : ℝ) ^ 2) ∧
      u' {none} ∈ Set.Icc ((H.α : ℝ) * (H.η : ℝ) ^ 2) (2 * (H.α : ℝ) * (H.η : ℝ) ^ 2))
    (h₂' : H.branch = .gen →
      u Finset.univ ∈ Set.Icc ((H.α : ℝ) * (H.η : ℝ) ^ 2) (2 * (H.α : ℝ) * (H.η : ℝ) ^ 2) ∧
      u' Finset.univ ∈ Set.Icc ((H.α : ℝ) * (H.η : ℝ) ^ 2) (2 * (H.α : ℝ) * (H.η : ℝ) ^ 2)) :
    ∀ i, i ≠ i₀ → ∀ v ∈ H.VH,
      Protocol.rootMsg M.protocol (M.prescribe i (H.vst0 v 0 0)) ≠
        Protocol.rootMsg M.protocol
          (M.prescribe i (H.vst0 v 0 ((m : ℝ) * H.α * (H.η : ℝ) ^ 3))) := by sorry

end DSICHardRev
