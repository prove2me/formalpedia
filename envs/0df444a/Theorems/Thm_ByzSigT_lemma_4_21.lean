-- Prove2me | Theorems.Thm_ByzSigT_lemma_4_21
-- name    : ByzSigT.lemma_4_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:00:58.204089+00:00
-- url     : https://prove2.me/theorems/9cd4099b-be66-48cb-8acb-0dc9fab65e42
-- title:
--   Lemma 4.21: every correct party reaches allgood or equiv
-- statement:
--   Let $k\ge 1$, $f<\frac{2^{k+1}-1}{2^{k+2}-1}n$, $\Delta>0$, and let $E$ be an execution of the $k$-SigT protocol with an $f$-bounded corrupt set $F$ and stabilization time $\mathrm{GST}\ge0$. Let $1\le i\le k$. Suppose no correct party decides in $E$ and every correct party enters layer $i$. Then every correct party multicasts an allgood or equiv message in layer $i$.
--
--   This is the liveness of a layer: it is where the view structure, the timers and the delay bound $\Delta$ after stabilization are used.
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
-- source:
--   Efron, Kelkar, Mutreja, Roughgarden, Byzantine Agreement with Signature Tokens, STOC 2027 submission (manuscript sha256 f020c58a…), Lemma 4.21, p.24 (PDF p.25), with the standing assumption of §4.2.2, p.23 (PDF p.24)

import Mathlib
import Definitions.Def_ByzSigT_ExistsIn

namespace ByzSigT

/-- **Lemma 4.21** (p.24, PDF p.25), under the standing assumption of §4.2.2 (p.23). Efron, Kelkar, Mutreja, Roughgarden, *Byzantine Agreement with Signature Tokens*, STOC 2027
submission (manuscript sha256 f020c58a…):

> We now prove that all correct parties eventually exit each layer i ≤ k. Fix such i, and assume
> that no correct party decides and that every correct party eventually enters layer i.

> Lemma 4.21. Eventually, every correct party multicasts an allgood or equiv message in layer i.

**Formalization Note.** The standing hypotheses are those of the analysis (p.18): `k ≥ 1`,
`f < (2^{k+1}−1)n/(2^{k+2}−1)` (cross-multiplied in `ℕ`), `Δ > 0`, an `f`-bounded corrupt set `F`,
`GST ≥ 0`, and an execution `E` of the k-SigT protocol `kSigT n f k Δ` (Algorithm 1), in which the
input conditions of every layer hold (Lemma 4.23). Layers are `≥ 1`. The message is the party's own (signed by it). -/
theorem lemma_4_21 {n f k : ℕ} {Δ GST : ℝ} {F : Finset (Fin n)} {u : Fin n → Bool} {E : Execution n k}
    (hk : 1 ≤ k) (hf : (2 ^ (k + 2) - 1) * f < (2 ^ (k + 1) - 1) * n) (hΔ : 0 < Δ)
    (hF : F.card ≤ f) (hGST : 0 ≤ GST) (hE : IsExecution (kSigT n f k Δ) F u GST Δ E)
    (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k)
    (hnd : ∀ p ∉ F, ∀ v : Bool, ¬ Decides (kSigT n f k Δ) u E p v)
    (hen : ∀ p ∉ F, EntersLayer f Δ u E p i) :
    ∀ p ∉ F, MulticastsAgEq f Δ u E p i := by sorry

end ByzSigT
