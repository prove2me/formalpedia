-- Prove2me | Theorems.Thm_ByzSigT_theorem_4_1
-- name    : ByzSigT.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:56:30.782698+00:00
-- url     : https://prove2.me/theorems/39eac105-9a9e-42c3-8ac2-faaee2e30965
-- title:
--   Theorem 4.1: a deterministic $f$-secure BA protocol from a PKI and $k$ signature tokens
-- statement:
--   Let $k\ge 1$, let $n,f$ be natural numbers with
--
--   $$f<\frac{2^{k+1}-1}{2^{k+2}-1}\,n,$$
--
--   and let $\Delta>0$. Then there is a deterministic well-formed protocol for $n$ parties with a PKI and a $k$-SigT setup that is $f$-secure in partial synchrony with delay bound $\Delta$: for every corrupt set with $|F|\le f$, all inputs, every $\mathrm{GST}\ge0$ and every execution, it satisfies agreement, termination and validity.
--
--   The protocol is chosen after $k,n,f,\Delta$ and before the adversary's choices. The resilience is $3/7$ for $k=1$, $7/15$ for $k=2$, and any $f<n/2$ for $k=\Theta(\log n)$; without tokens, partial synchrony allows only $f<n/3$ (Dwork, Lynch and Stockmeyer, 1988).
--
--   Differences from the source:
--   - generalization: “n is such that all fractions we consider are integers” (p.4) → no divisibility hypothesis on n and f; every comparison with a fraction is made in ℤ; reason: the fractions occur only inside inequalities, each step of the proof holds over ℚ, and the printed case is the instance where the fractions are integers
--   - encoding: f < (2^{k+1}−1)n/(2^{k+2}−1) → (2^{k+2}−1)·f < (2^{k+1}−1)·n in ℕ; reason: cross-multiplied by a positive number; the same pairs (n, f)
--   - reading: a PKI of digital signatures and a SigT environment (§2) → symbolic terms `sig q t` and `tok q i t`, which cannot be forged and whose contents can be read; corrupt parties send any term derivable from all traffic of correct parties and their own keys, with at most one content per corrupt party and token index; reason: the paper's own idealization: its proofs treat a proof of corruption as certain, the theorem has no negligible error term, and §1.2 treats the SigT as a black box
--   - reading: hardware clocks with arbitrary skew and drift before GST and no drift after (p.4) → relative timers: a timer of duration d set at time τ fires in [τ, max(τ, GST) + d], and exactly at τ + d when τ ≥ GST; reason: this contains every clock behaviour the paper allows, and Algorithms 1 and 2 use only relative waits
--   - reading: executions in real time, with “received by time τ” (pp.4, 24) → a sequence of events indexed by ℕ with non-decreasing, unbounded real times; simultaneous events are ordered by the adversary, except that a timer of a correct party firing at τ is handled after the deliveries to it at τ of messages sent before the timer event; reason: “by time τ” means available at τ (p.24 uses this for the Wait 2∆); without the exception an adversary who delivers exactly at the deadline can make a correct leader miss a suggest in every view it leads, and Lemma 4.21 would fail for the printed protocol
--   - generalization: a message reaches its destination; the adversary controls the corrupt parties (p.4) → the adversary also sees every message a correct party sends, may deliver a message of a correct party several times within the model's bounds, and may fire a timer several times inside its window; reason: every execution of the paper's model is an execution here, so the statement covers more executions
--   - reading: “assuming a PKI and a k-SigT setup, there exists a deterministic … protocol” → ∃ P, P.WellFormed ∧ Secure P f Δ, where well-formed means that every term sent or token-signed is derivable by the party, and timer durations are bounded below by a positive constant; reason: without derivability a protocol could forge tokens and the setup would mean nothing; without the timer bound a protocol could have no executions and be secure vacuously
--   - reading: “f-secure” (proof of Theorem 4.1, p.26) with a known Δ (p.4) → the protocol may depend on k, n, f and Δ; GST and the adversary's choices come after it; reason: Δ is known to the parties and GST is not (p.4)
-- source:
--   Efron, Kelkar, Mutreja, Roughgarden, Byzantine Agreement with Signature Tokens, STOC 2027 submission (manuscript sha256 f020c58a…), Theorem 4.1, p.12 (PDF p.13); Theorem 1.1, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_ByzSigT_Secure

namespace ByzSigT

/-- **Theorem 4.1** (p.12, PDF p.13; also Theorem 1.1, p.2). Efron, Kelkar, Mutreja, Roughgarden, *Byzantine Agreement with Signature Tokens*, STOC 2027
submission (manuscript sha256 f020c58a…):

> Let k ≥ 1 and f < (2^{k+1}−1)/(2^{k+2}−1) n. Then, assuming a PKI and a k-SigT setup, there
> exists a deterministic f-secure BA protocol in partial synchrony.

**Formalization Note.** The protocol is chosen after `k, n, f, Δ` and before the adversary's corrupt
set, inputs, GST and execution (`Secure`). It must be well-formed: it sends and token-signs only
terms derivable from what it received and its own token replies, so it cannot forge tokens. The
bound is `(2^{k+2} − 1)·f < (2^{k+1} − 1)·n` in `ℕ` (equivalent since `2^{k+2} − 1 > 0`); there is
no hypothesis that the fractions of the analysis are integers (p.4). -/
theorem theorem_4_1 (k : ℕ) (hk : 1 ≤ k) (n f : ℕ)
    (hf : (2 ^ (k + 2) - 1) * f < (2 ^ (k + 1) - 1) * n) (Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ P : Protocol n k, P.WellFormed ∧ Secure P f Δ := by sorry

end ByzSigT
