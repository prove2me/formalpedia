-- Prove2me | Theorems.Thm_DPVerify_theorem_4_1
-- name    : DPVerify.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:54:36.570303+00:00
-- url     : https://prove2.me/theorems/f3719876-45dc-4ab9-9dc4-efd9e8aaf2cb
-- title:
--   Theorem 4.1 — a replicable one-round private-coin proof becomes a $(4\varepsilon,120\pi\delta)$-DP AM proof (corrected: the whole protocol is (ε, δ)-DP)
-- statement:
--   There is a universal constant $K$ such that the following holds. Let $P$ be a one-round private-coin protocol with sample complexity $s$ and communication complexity $C$ that is $(\varepsilon,\delta)$-differentially private, $\varepsilon,\delta\ge0$. Then there is a one-round public-coin (AM) protocol $Q$ on the same $s$ samples such that
--
--   1. $Q$ is $(4\varepsilon,120\pi\delta)$-differentially private;
--   2. $Q$ has communication complexity at most $K\cdot C$;
--   3. for every $\rho\le10^{-4}$ and every distribution $D$ at which some randomized algorithm with the same message law as $P$ on every sample is $\rho$-replicable:
--      - (completeness) if some prover makes $P$ accept with probability at least $0.999$ under $D$, then some prover makes $Q$ accept with probability at least $0.733$;
--      - (soundness) if every prover makes $P$ accept with probability at most $0.001$ under $D$, then every prover makes $Q$ accept with probability at most $0.0943$.
--
--   The protocol $Q$ does not depend on $D$. This is the reduction at the heart of the paper: replicability of the verifier's message lets the verifier send only its random seed and have the prover propose the whole transcript, accepted through a smooth consistency gate.
--
--   Differences from the source:
--   - correction: $\mathcal A(S,r)$ is a $\rho$-replicable, $(\varepsilon,\delta)$-DP algorithm (only the message algorithm is private) → the whole one-round protocol is $(\varepsilon,\delta)$-DP; reason: the printed statement is false: with $\mathcal X=\{0,1\}$, $s=10$, a constant message (which is $0$-replicable and $(0,0)$-DP) and a verifier accepting iff all ten samples are $0$, completeness holds at the point mass at $0$ and soundness $2^{-10}\le0.001$ holds at every $D$ with $D\{1\}\ge1/2$, but no $(0,0)$-DP AM protocol has completeness $0.733$ at the first and soundness $0.0943$ at the second, since against a fixed prover its acceptance probability is the same on every sample (substitutions connect any two samples), so a prover at the second distribution can copy the honest prover at the first; the privacy proof (p.15) uses that $q_S(m,a)$ and $p_S(m)-q_S(m,a)$ change by at most $e^\varepsilon$, which is privacy of the whole protocol, and this is the hypothesis of Corollary 4.5
--   - generalization: $\mathcal A$ is $\rho$-replicable → for the given $D$, some randomized algorithm with the same message law as $\mathcal A(S,\cdot)$ on every sample is $\rho$-replicable at $D$; reason: the proof uses replicability only through $\mathbb E_Sd_{TV}(p_S,\mu)\le\rho$ (p.12), which depends only on the message laws; taking $\mathcal A$ itself gives the printed hypothesis, and Corollary 4.5 needs the algorithm of Lemma 4.4
--   - generalization: $\mathcal D$ satisfies the property / is $\xi$-far from it; one population distribution $\mathcal D$ → every distribution $D$ at which the original protocol has completeness $0.999$ (resp. soundness $0.001$); one protocol $Q$ for all $D$ and all $\rho\le10^{-4}$; reason: the property enters the proof only through these guarantees; the printed statement is the case of a single $D$
--   - reading: an AM protocol in which the verifier sends only random string $r\sim\mathcal R$ → the verifier's only message is a string of uniformly random public bits; reason: the definition of AM protocols in §2 (p.4)
--   - generalization: communication complexity $O(C)+\log|\mathcal R|$ → at most $K\cdot C$ for a universal $K$; reason: implies the printed bound; p.11 notes a pairwise-independent hash family needs only $O(\log|\mathcal M|)=O(C)$ public bits
--   - reading: $(\varepsilon,\delta)$ → $\varepsilon,\delta\ge0$; reason: privacy parameters are nonnegative throughout the paper
--   - reading: adjacent datasets differ by the addition or removal of one element (Definition 2.1) → neighbouring samples in $\mathcal X^s$ differ in one coordinate; reason: every protocol of the paper reads a sample of fixed size, and §6 (p.33) proves privacy for neighbouring datasets which differ on the $i$th coordinate
--   - generalization: seeds $r\sim\mathcal R$ with $|\mathcal R|$ the support size of the random seeds (p.11) → seeds from any probability space, with the message and the acceptance probability jointly measurable; reason: the proof uses the seeds only through $p_S$ and $q_S$, which every seed law defines, and the communication bound does not involve them; a finitely supported seed law is the case of a finite type with its discrete σ-algebra
--   - encoding: interactive protocols, adversaries and transcripts (Definition 2.2) → finite message and reply types; transcripts (message, reply, decision bit); deterministic prover strategies; the verifier's fresh coins folded into an acceptance probability in $[0,1]$, jointly measurable in the sample and the seed; reason: Lean representation; randomized provers are mixtures of deterministic ones and the DP inequality is preserved under mixtures, so no instance changes
-- source:
--   Du, Dwork, Tankala, Zhang, Differentially Private Verification of Distribution Properties, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Theorem 4.1, pp.10–11 (PDF pp.13–14)

import Mathlib
import Definitions.Def_DPVerify_RandAlg
import Definitions.Def_DPVerify_IsReplicableAt
import Definitions.Def_DPVerify_OneRoundProtocol
import Definitions.Def_DPVerify_OneRoundProtocol_IsDP
import Definitions.Def_DPVerify_AMProtocol
import Definitions.Def_DPVerify_AMProtocol_IsDP

set_option autoImplicit false

open MeasureTheory

namespace DPVerify

/-- Theorem 4.1, corrected (Du, Dwork, Tankala, Zhang, *Differentially Private Verification of Distribution Properties*, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), pp.10–11 = PDF pp.13–14): a one-round `(ε, δ)`-DP private-coin
protocol whose message algorithm is `ρ`-replicable converts to a `(4ε, 120πδ)`-DP public-coin
protocol on the same `s` samples. There is a universal `K` such that every such protocol `P` has
an AM protocol `Q` with `Q.comm ≤ K · P.comm` such that, for `ρ ≤ 10⁻⁴` and every distribution `D`
at which some algorithm with the same message law as `P` is `ρ`-replicable:
* if some prover makes `P` accept with probability `≥ 0.999` under `D`, some prover makes `Q`
  accept with probability `≥ 0.733`;
* if every prover makes `P` accept with probability `≤ 0.001` under `D`, every prover makes `Q`
  accept with probability `≤ 0.0943`.

**Formalization Note**
* Correction: the printed hypothesis is only that the message algorithm `A` is `(ε, δ)`-DP. That
  is false: with `X = {0,1}`, `s = 10`, a constant message and a verifier accepting iff all ten
  samples are `0`, completeness and soundness hold for `Yes = {δ₀}`, `No = {D : D{1} ≥ 1/2}`,
  but no `(0, 0)`-DP AM protocol separates them. The privacy proof (p.15) uses DP of the whole
  protocol, which is assumed here.
* Replicability enters only through the law of the message (p.12), and is assumed per `D` for
  any algorithm with the same message law as `P` on every sample.
* The AM protocol is fixed before `D`. Its communication bound `≤ K · C` implies the printed
  `O(C) + log |R|`.
* "Satisfies the property" and "`ξ`-far" are replaced by the original guarantees at `D`. -/
theorem theorem_4_1 :
    ∃ K : ℕ, ∀ (X : Type) [MeasurableSpace X] (s : ℕ) (P : OneRoundProtocol X s) (ε δ : ℝ),
      0 ≤ ε → 0 ≤ δ → P.IsDP ε δ →
      ∃ Q : AMProtocol X s, Q.IsDP (4 * ε) (120 * Real.pi * δ) ∧ Q.comm ≤ K * P.comm ∧
        ∀ ρ : ℝ, ρ ≤ 1 / 10 ^ 4 → ∀ D : ProbabilityMeasure X,
          (∃ A : RandAlg X P.M s, (∀ S, A.law S = P.msgLaw S) ∧ IsReplicableAt A D ρ) →
          ((∃ f : P.M → P.Ans, 0.999 ≤ P.accept f D) →
              ∃ g : (Fin Q.nbits → Bool) → Q.B, 0.733 ≤ Q.accept g D) ∧
          ((∀ f : P.M → P.Ans, P.accept f D ≤ 0.001) →
              ∀ g : (Fin Q.nbits → Bool) → Q.B, Q.accept g D ≤ 0.0943) := by sorry

end DPVerify
