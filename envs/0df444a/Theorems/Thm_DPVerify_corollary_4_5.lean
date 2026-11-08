-- Prove2me | Theorems.Thm_DPVerify_corollary_4_5
-- name    : DPVerify.corollary_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:54:23.457172+00:00
-- url     : https://prove2.me/theorems/7da70ed8-0dfd-480d-a4cb-308a547ec93e
-- title:
--   Corollary 4.5 — for $\varepsilon=O(1/\sqrt s)$, $\delta=O(1/s^{5/2})$, a one-round $(\varepsilon,\delta)$-DP private-coin proof becomes a $(4\varepsilon,120\pi\delta)$-DP public-coin proof
-- statement:
--   There are universal constants $c_1,c_2>0$ and $K$ such that the following holds. Let $\mathcal X$ be a measurable space, $s\ge1$, and let $P$ be a one-round private-coin interactive proof with sample complexity $s$ and communication complexity $c$ that is $(\varepsilon,\delta)$-differentially private with
--
--   $$
--   0\le\varepsilon\le\frac{c_1}{\sqrt s},\qquad 0\le\delta\le\frac{c_2}{s^{5/2}} .
--   $$
--
--   Let $\mathsf{Yes}$ and $\mathsf{No}$ be sets of distributions on $\mathcal X$ such that $P$ verifies the property: for every $D\in\mathsf{Yes}$ some prover makes the verifier accept with probability at least $0.999$, and for every $D\in\mathsf{No}$ every prover makes it accept with probability at most $0.001$. Then there is a one-round public-coin interactive proof $Q$ with the same sample complexity $s$ such that
--
--   1. $Q$ is $(4\varepsilon,120\pi\delta)$-differentially private;
--   2. $Q$ has communication complexity at most $K\cdot c$;
--   3. for every $D\in\mathsf{Yes}$ some prover makes $Q$ accept with probability at least $0.733$;
--   4. for every $D\in\mathsf{No}$ every prover makes $Q$ accept with probability at most $0.0943$.
--
--   This is the paper's main result: in the regime $\varepsilon=O(1/\sqrt s)$, $\delta=O(1/s^{5/2})$, private coins give a differentially private verifier no power beyond public coins, at a constant-factor cost in privacy and communication and none in samples.
--
--   Differences from the source:
--   - reading: $\varepsilon=O(1/\sqrt s)$ and $\delta=O(1/s^{5/2})$ → $0\le\varepsilon\le c_1/\sqrt s$ and $0\le\delta\le c_2/s^{5/2}$ with $c_1,c_2>0$ chosen before $\mathcal X$, $s$ and the protocol; reason: the only reading with content; the proof plugs fixed small values into Lemmas 4.2–4.4
--   - reading: an interactive proof verifying property $P$ (no error levels named) → completeness $\ge0.999$ and soundness $\le0.001$ for the given proof; $\ge0.733$ and $\le0.0943$ for the new one; reason: the corollary's proof goes through Theorem 4.1, which fixes these levels
--   - generalization: the distributions satisfying $P$ and those $\xi$-far from $P$ → any two sets $\mathsf{Yes}$, $\mathsf{No}$ of distributions; reason: the property enters only through these two sets; taking $\mathsf{Yes}=P$ and $\mathsf{No}$ the $\xi$-far distributions gives the printed statement
--   - reading: communication complexity $c$ → at most $K\cdot c$ for a universal $K$; reason: the introduction (p.2) claims "only a constant factor increase in its privacy parameters, sample complexity, and communication complexity", and Theorem 4.1 gives $O(C)+\log|\mathcal R|$
--   - encoding: sample complexity $s$ → $s\ge1$; reason: at $s=0$ the bounds $c_1/\sqrt s$, $c_2/s^{5/2}$ divide by zero
--   - reading: adjacent datasets differ by the addition or removal of one element (Definition 2.1) → neighbouring samples in $\mathcal X^s$ differ in one coordinate; reason: every protocol of the paper reads a sample of fixed size, and §6 (p.33) proves privacy for neighbouring datasets which differ on the $i$th coordinate
--   - generalization: seeds $r\sim\mathcal R$ with $|\mathcal R|$ the support size of the random seeds (p.11) → seeds from any probability space, with the message and the acceptance probability jointly measurable; reason: the proof uses the seeds only through $p_S$ and $q_S$, which every seed law defines, and the communication bound does not involve them; a finitely supported seed law is the case of a finite type with its discrete σ-algebra
--   - encoding: interactive protocols, adversaries and transcripts (Definition 2.2) → finite message and reply types; transcripts (message, reply, decision bit); deterministic prover strategies; the verifier's fresh coins folded into an acceptance probability in $[0,1]$, jointly measurable in the sample and the seed; reason: Lean representation; randomized provers are mixtures of deterministic ones and the DP inequality is preserved under mixtures, so no instance changes
-- source:
--   Du, Dwork, Tankala, Zhang, Differentially Private Verification of Distribution Properties, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Corollary 4.5, p.18 (PDF p.21); Theorem 4.1, pp.10–11 (PDF pp.13–14)

import Mathlib
import Definitions.Def_DPVerify_OneRoundProtocol
import Definitions.Def_DPVerify_OneRoundProtocol_IsDP
import Definitions.Def_DPVerify_AMProtocol
import Definitions.Def_DPVerify_AMProtocol_IsDP

set_option autoImplicit false

open MeasureTheory

namespace DPVerify

/-- Corollary 4.5 (Du, Dwork, Tankala, Zhang, *Differentially Private Verification of Distribution Properties*, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), p.18 = PDF p.21): "Given a one-round `(ε, δ)`-DP interactive proof verifying
property `P` with sample complexity `s` and communication complexity `c` with `ε = O(1/√s)` and
`δ = O(1/s^{5/2})`, there exists a one-round `(4ε, 120πδ)`-DP public coin interactive proof
verifying property `P` with sample complexity `s` and communication complexity `c`."

There are universal constants `c₁, c₂ > 0` and `K` such that: for every measurable space `X`,
every `s ≥ 1`, and every one-round private-coin protocol `P` on `s` samples that is `(ε, δ)`-DP with
`0 ≤ ε ≤ c₁/√s` and `0 ≤ δ ≤ c₂/s^{5/2}`, and for every two sets `Yes`, `No` of distributions on `X`
on which `P` has completeness `0.999` and soundness `0.001`, there is a one-round public-coin
protocol `Q` on the same `s` samples that is `(4ε, 120πδ)`-DP, uses at most `K · c` bits of
communication, and has completeness `0.733` on `Yes` and soundness `0.0943` on `No`.

**Formalization Note**
* `O(·)` is read with `c₁, c₂` quantified before `X`, `s` and the protocol.
* "Verifying property `P`" is read with the error levels of Theorem 4.1, the only route the paper
  gives: completeness `≥ 0.999` and soundness `≤ 0.001` for the given proof, `≥ 0.733` and
  `≤ 0.0943` for the new one. The property and "`ξ`-far" enter only as the set `Yes` of
  distributions in the property and the set `No` of distributions far from it; any two sets are
  allowed.
* "Communication complexity `c`" is read as `≤ K · c` (p.2: "a constant factor increase in its
  privacy parameters, sample complexity, and communication complexity"; Theorem 4.1 gives
  `O(C) + log |R|`).
* Adjacency is substitution of one sample entry; transcripts record message, reply and decision
  bit, and DP quantifies over every prover strategy. -/
theorem corollary_4_5 :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ K : ℕ,
      ∀ (X : Type) [MeasurableSpace X] (s : ℕ), 0 < s →
      ∀ (P : OneRoundProtocol X s) (ε δ : ℝ),
        0 ≤ ε → ε ≤ c₁ / Real.sqrt s → 0 ≤ δ → δ ≤ c₂ / (s : ℝ) ^ ((5 : ℝ) / 2) →
        P.IsDP ε δ →
      ∀ Yes No : Set (ProbabilityMeasure X),
        (∀ D ∈ Yes, ∃ f : P.M → P.Ans, 0.999 ≤ P.accept f D) →
        (∀ D ∈ No, ∀ f : P.M → P.Ans, P.accept f D ≤ 0.001) →
        ∃ Q : AMProtocol X s, Q.IsDP (4 * ε) (120 * Real.pi * δ) ∧ Q.comm ≤ K * P.comm ∧
          (∀ D ∈ Yes, ∃ g : (Fin Q.nbits → Bool) → Q.B, 0.733 ≤ Q.accept g D) ∧
          (∀ D ∈ No, ∀ g : (Fin Q.nbits → Bool) → Q.B, Q.accept g D ≤ 0.0943) := by sorry

end DPVerify
