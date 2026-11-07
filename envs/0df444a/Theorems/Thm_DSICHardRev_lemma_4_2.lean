-- Prove2me | Theorems.Thm_DSICHardRev_lemma_4_2
-- name    : DSICHardRev.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:36:48.045461+00:00
-- url     : https://prove2.me/theorems/fdcac4c5-0e64-4fe3-a11e-03f9a28756b7
-- title:
--   Lemma 4.2 — a node of first non-trivial communication with a scale $s^\dagger$
-- statement:
--   Let $\eta\ge800$ and $\alpha\eta\le m$, let $\mathcal H$ be an $(\alpha,\eta,\lambda,C,\mathcal U)$-KSSHD using GS, XOS or general valuations, and let $\mathrm{MECH}'$ be a deterministic, IR, NNT, DSIC mechanism for the bidders of $\mathcal H$ on $M=[m]\cup\{\dagger\}$ that attains an $\eta/800$-approximation using $\Gamma\le2^{m/2}$ communication on $\mathcal V[-2^m,2^m](\mathcal H)$. Then there exist a node $\mathcal N^\dagger$ of its protocol, a bidder $i^\dagger$, $u,u'\in\mathcal V(\mathcal H)$, integers $a,a',s^\dagger\in[-2^m,2^m]$ and integers $b,b'\in[0,m^4]$ such that
--
--   1. at $\mathcal N^\dagger$ the messages prescribed to $i^\dagger$ for $u_{a,b}$ and $u'_{a',b'}$ are different;
--   2. $u_{a,b}(\{\dagger\}),u'_{a',b'}(\{\dagger\})\in[2^{s^\dagger/2}\alpha\eta^2,\,2^{s^\dagger/2+1}\alpha\eta^2]$ if the valuations are GS or XOS, and $u_{a,b}(M),u'_{a',b'}(M)$ lie in that interval if they are general;
--   3. $a,a'\in[s^\dagger-m,\,s^\dagger+m]$;
--   4. every profile of valuations from $\mathcal V[s^\dagger-m,s^\dagger+m](\mathcal H)$ reaches $\mathcal N^\dagger$.
--
--   For general valuations $u_{a,b}$ denotes some $u_{a,b,X,Y}$ with nonempty $X,Y$. This is the first step of the proof of Proposition 4.1.
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
--   - reading: a, a′, s† ∈ [−2^m, 2^m] and b, b′ ∈ [m⁴] ∪ {0} → a, a′, s† integers in [−2^m, 2^m] and b, b′ natural numbers ≤ m⁴; reason: u_{a,b} is a member of V[s⁻, s⁺](H), whose scales are integers (s ∈ ℤ ∩ [s⁻, s⁺], t ∈ ℤ ∩ [0, m⁴], pp.16–17), and the integrality convention (p.7); integer witnesses are in particular the printed ones
--   - reading: u_{a,b} for general valuations ("we abuse notation ... let v_{s,t} denote arbitrary v_{s,t,X,Y}", p.17) → u_{a,b,X,Y} and u′_{a′,b′,X′,Y′} for some nonempty X, Y, X′, Y′ ⊆ M; for GS/XOS valuations the sets are unused; reason: the paper's abuse of notation, read existentially
--   - encoding: the message sent at the node N† → rootMsg of the restriction of the prescribed strategy to the subtree at N† (none at a leaf); reason: a strategy assigns a message to every node; a leaf sends none, so clause 1 forces N† to be internal
--   - reading: using Γ communication → communication ≤ Γ; reason: "using X communication" bounds the worst-case transcript length (Definition 2.7)
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), §4.2, p.17, Lemma 4.2 (inside the proof of Proposition 4.1, with its hypotheses)

import Mathlib
import Definitions.Def_DSICHardRev_Protocol
import Definitions.Def_DSICHardRev_ReductionClass

namespace DSICHardRev

/-- **Lemma 4.2** (F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…), §4.2, p.17), inside the proof of Proposition 4.1:
there exist a node `N†` of the protocol of `MECH′`, a bidder `i†`, `u, u′ ∈ V(H)`,
`a, a′, s† ∈ [−2^m, 2^m]` and `b, b′ ∈ [m⁴] ∪ {0}` such that
(1) at `N†` the messages prescribed to `i†` for `u_{a,b}` and `u′_{a′,b′}` differ;
(2) `u_{a,b}({†}), u′_{a′,b′}({†}) ∈ [2^{s†/2} αη², 2^{s†/2+1} αη²]` (GS or XOS), or
`u_{a,b}(M), u′_{a′,b′}(M) ∈ [2^{s†/2} αη², 2^{s†/2+1} αη²]` (general);
(3) `a, a′ ∈ [s† − m, s† + m]`;
(4) every profile of valuations from `V[s† − m, s† + m](H)` reaches `N†`.

**Formalization Note.** The hypotheses are those of Proposition 4.1: \`η ≥ 800\`, \`αη ≤ m\`, \`H\`
any KSSHD (GS, XOS or general), \`MECH′\` a mechanism for the bidders of \`H\` on the items
\`[m] ∪ {†}\` (\`Option (Fin m)\`, \`none = †\`), deterministic by construction, IR, NNT, DSIC and
attaining an \`η/800\`-approximation on \`V[−2^m, 2^m](H)\`, with communication \`≤ Γ ≤ 2^{m/2}\`. `a, a′, s†` are integers and `b, b′` naturals `≤ m⁴`. For general valuations `u_{a,b}`
stands for some `u_{a,b,X,Y}` with `X, Y ≠ ∅` (the paper's abuse of notation); for GS/XOS valuations
the sets `X, Y` are unused. The message at `N†` is `rootMsg` of the restriction of the strategy to the
subtree at `N†`. -/
theorem lemma_4_2 {m : ℕ} (H : KSSHD m) (hη : 800 ≤ H.η) (hαη : H.α * H.η ≤ m)
    (M' : Mechanism H.Bidder (Option (Fin m))) (Γ : ℝ)
    (hIR : M'.IsIR (H.Vrange (-(2 : ℤ) ^ m) ((2 : ℤ) ^ m)))
    (hNNT : M'.IsNNT (H.Vrange (-(2 : ℤ) ^ m) ((2 : ℤ) ^ m)))
    (hDSIC : M'.IsDSIC (H.Vrange (-(2 : ℤ) ^ m) ((2 : ℤ) ^ m)))
    (hApprox : M'.IsApprox (H.Vrange (-(2 : ℤ) ^ m) ((2 : ℤ) ^ m)) ((H.η : ℝ) / 800))
    (hcomm : (M'.comm : ℝ) ≤ Γ) (hΓ : Γ ≤ (2 : ℝ) ^ ((m : ℝ) / 2)) :
    ∃ (q : M'.protocol.Pos) (i₀ : H.Bidder) (u u' : Finset (Fin m) → ℝ) (a a' s₀ : ℤ) (b b' : ℕ)
      (X Y X' Y' : Finset (Option (Fin m))),
      u ∈ H.VH ∧ u' ∈ H.VH ∧ X.Nonempty ∧ Y.Nonempty ∧ X'.Nonempty ∧ Y'.Nonempty ∧
      -(2 : ℤ) ^ m ≤ a ∧ a ≤ (2 : ℤ) ^ m ∧ -(2 : ℤ) ^ m ≤ a' ∧ a' ≤ (2 : ℤ) ^ m ∧
      -(2 : ℤ) ^ m ≤ s₀ ∧ s₀ ≤ (2 : ℤ) ^ m ∧ b ≤ m ^ 4 ∧ b' ≤ m ^ 4 ∧
      Protocol.rootMsg (M'.protocol.subtree q)
          (Protocol.Strat.restrict M'.protocol (M'.prescribe i₀ (H.vst u a b X Y)) q) ≠
        Protocol.rootMsg (M'.protocol.subtree q)
          (Protocol.Strat.restrict M'.protocol (M'.prescribe i₀ (H.vst u' a' b' X' Y')) q) ∧
      (H.branch ≠ .gen →
        H.vst u a b X Y {none} ∈ Set.Icc ((2 : ℝ) ^ ((s₀ : ℝ) / 2) * H.α * (H.η : ℝ) ^ 2)
          ((2 : ℝ) ^ ((s₀ : ℝ) / 2 + 1) * H.α * (H.η : ℝ) ^ 2) ∧
        H.vst u' a' b' X' Y' {none} ∈ Set.Icc ((2 : ℝ) ^ ((s₀ : ℝ) / 2) * H.α * (H.η : ℝ) ^ 2)
          ((2 : ℝ) ^ ((s₀ : ℝ) / 2 + 1) * H.α * (H.η : ℝ) ^ 2)) ∧
      (H.branch = .gen →
        H.vst u a b X Y Finset.univ ∈ Set.Icc ((2 : ℝ) ^ ((s₀ : ℝ) / 2) * H.α * (H.η : ℝ) ^ 2)
          ((2 : ℝ) ^ ((s₀ : ℝ) / 2 + 1) * H.α * (H.η : ℝ) ^ 2) ∧
        H.vst u' a' b' X' Y' Finset.univ ∈ Set.Icc ((2 : ℝ) ^ ((s₀ : ℝ) / 2) * H.α * (H.η : ℝ) ^ 2)
          ((2 : ℝ) ^ ((s₀ : ℝ) / 2 + 1) * H.α * (H.η : ℝ) ^ 2)) ∧
      s₀ - m ≤ a ∧ a ≤ s₀ + m ∧ s₀ - m ≤ a' ∧ a' ≤ s₀ + m ∧
      ∀ v : H.Bidder → Finset (Option (Fin m)) → ℝ,
        (∀ i, v i ∈ H.Vrange (s₀ - m) (s₀ + m)) →
          M'.protocol.Reaches (fun i => M'.prescribe i (v i)) q := by sorry

end DSICHardRev
