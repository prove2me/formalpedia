-- Prove2me | Theorems.Thm_ByzSigT_claim_4_4
-- name    : ByzSigT.claim_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:59:46.211795+00:00
-- url     : https://prove2.me/theorems/f6c098f0-29f6-4d8e-9c0d-006dd90d1524
-- title:
--   Claim 4.4: conflicting certificates identify a large corrupt set
-- statement:
--   Let $k\ge 1$, $f<\frac{2^{k+1}-1}{2^{k+2}-1}n$, $\Delta>0$, and let $E$ be an execution of the $k$-SigT protocol with an $f$-bounded corrupt set $F$ and stabilization time $\mathrm{GST}\ge0$. Let $\sigma_a,\sigma_b$ be conflicting certificates of a layer $i$ that are present in $E$. Then $\sigma_a$ and $\sigma_b$ together prove corrupt every party of
--
--   $$B=D_{\sigma_a}\cup D_{\sigma_b}\cup\bigl(\mathrm{signers}(\sigma_a)\cap\mathrm{signers}(\sigma_b)\bigr),$$
--
--   this set lies in $F$, and
--
--   $$|B|\ge n-2f+|D_{\sigma_a}|+|D_{\sigma_b}|.$$
--
--   This is the basic counting fact of the protocol: every equivocation that forms conflicting certificates exposes at least $n-2f$ parties beyond those the certificates already expose. Lemmas 4.8 and 4.11 compound it across layers.
--
--   Differences from the source:
--   - generalization: “n is such that all fractions we consider are integers” (p.4) → no divisibility hypothesis on n and f; every comparison with a fraction is made in ℤ; reason: the fractions occur only inside inequalities, each step of the proof holds over ℚ, and the printed case is the instance where the fractions are integers
--   - encoding: f < (2^{k+1}−1)n/(2^{k+2}−1) → (2^{k+2}−1)·f < (2^{k+1}−1)·n in ℕ; reason: cross-multiplied by a positive number; the same pairs (n, f)
--   - reading: a PKI of digital signatures and a SigT environment (§2) → symbolic terms `sig q t` and `tok q i t`, which cannot be forged and whose contents can be read; corrupt parties send any term derivable from all traffic of correct parties and their own keys, with at most one content per corrupt party and token index; reason: the paper's own idealization: its proofs treat a proof of corruption as certain, the theorem has no negligible error term, and §1.2 treats the SigT as a black box
--   - reading: hardware clocks with arbitrary skew and drift before GST and no drift after (p.4) → relative timers: a timer of duration d set at time τ fires in [τ, max(τ, GST) + d], and exactly at τ + d when τ ≥ GST; reason: this contains every clock behaviour the paper allows, and Algorithms 1 and 2 use only relative waits
--   - reading: executions in real time, with “received by time τ” (pp.4, 24) → a sequence of events indexed by ℕ with non-decreasing, unbounded real times; simultaneous events are ordered by the adversary, except that a timer of a correct party firing at τ is handled after the deliveries to it at τ of messages sent before the timer event; reason: “by time τ” means available at τ (p.24 uses this for the Wait 2∆); without the exception an adversary who delivers exactly at the deadline can make a correct leader miss a suggest in every view it leads, and Lemma 4.21 would fail for the printed protocol
--   - generalization: a message reaches its destination; the adversary controls the corrupt parties (p.4) → the adversary also sees every message a correct party sends, may deliver a message of a correct party several times within the model's bounds, and may fire a timer several times inside its window; reason: every execution of the paper's model is an execution here, so the statement covers more executions
--   - reading: Algorithm 1 and Algorithm 2 as pseudocode (pp.14–18) → the event handler `kSigT`: “received” means occurring in a term the party holds, including its own messages; “any”/“a” choices are made by a fixed choice function; a SigT use blocks the layer rules until the reply; a party forwards each received term once and, after deciding, ignores all events; reason: the pseudocode leaves these points open and the paper's arguments do not depend on them
--   - reading: “Statements about a layer i assume its input conditions” (p.18) → the statement is about every execution of the whole protocol (Algorithm 1 running every layer), with no input conditions as hypotheses; reason: the input conditions hold in every layer of such an execution, by Lemma 4.23 and the paragraph after it (p.25); “m exists in E” is defined for executions of the protocol (p.15)
--   - reading: “σ_a and σ_b together identify B” → B lies in the corrupt set of the tuple ⟨σ_a, σ_b⟩, for certificates each of whose messages exists in E; reason: “identify” is what a pair of certificates proves, and B ⊆ F is a claim about the execution
-- source:
--   Efron, Kelkar, Mutreja, Roughgarden, Byzantine Agreement with Signature Tokens, STOC 2027 submission (manuscript sha256 f020c58a…), Claim 4.4, p.18 (PDF p.19)

import Mathlib
import Definitions.Def_ByzSigT_ExistsIn

namespace ByzSigT

/-- **Claim 4.4** (p.18, PDF p.19). Efron, Kelkar, Mutreja, Roughgarden, *Byzantine Agreement with Signature Tokens*, STOC 2027
submission (manuscript sha256 f020c58a…):

> Let σ_a, σ_b be conflicting certificates of layer i, with corrupt sets D_σa, D_σb. Then σ_a and σ_b
> together identify B = D_σa ∪ D_σb ∪ (signers(σ_a) ∩ signers(σ_b)) ⊆ F, and
> |B| ≥ n − 2f + |D_σa| + |D_σb|.

**Formalization Note.** The standing hypotheses are those of the analysis (p.18): `k ≥ 1`,
`f < (2^{k+1}−1)n/(2^{k+2}−1)` (cross-multiplied in `ℕ`), `Δ > 0`, an `f`-bounded corrupt set `F`,
`GST ≥ 0`, and an execution `E` of the k-SigT protocol `kSigT n f k Δ` (Algorithm 1), in which the
input conditions of every layer hold (Lemma 4.23). The certificates are present in `E` (each of their messages
exists). "Identify" is: every party of `B` is proved corrupt by the pair, i.e. lies in the corrupt
set of the tuple `⟨σ_a, σ_b⟩`. The bound is in `ℤ`. -/
theorem claim_4_4 {n f k : ℕ} {Δ GST : ℝ} {F : Finset (Fin n)} {u : Fin n → Bool} {E : Execution n k}
    (hk : 1 ≤ k) (hf : (2 ^ (k + 2) - 1) * f < (2 ^ (k + 1) - 1) * n) (hΔ : 0 < Δ)
    (hF : F.card ≤ f) (hGST : 0 ≤ GST) (hE : IsExecution (kSigT n f k Δ) F u GST Δ E)
    (i : ℕ) (σa σb : Term n k) (hc : Conflicting f i σa σb)
    (ha : Present f Δ F u E σa) (hb : Present f Δ F u E σb) :
    (corruptSet f σa ∪ corruptSet f σb ∪ (certSigners σa ∩ certSigners σb)) ⊆
        corruptSet f (.list [σa, σb]) ∧
      (corruptSet f σa ∪ corruptSet f σb ∪ (certSigners σa ∩ certSigners σb)) ⊆ F ∧
      (n : ℤ) - 2 * f + (corruptSet f σa).card + (corruptSet f σb).card ≤
        ((corruptSet f σa ∪ corruptSet f σb ∪ (certSigners σa ∩ certSigners σb)).card : ℤ) := by sorry

end ByzSigT
