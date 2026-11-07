-- Prove2me | Theorems.Thm_ByzSigT_lemma_4_13
-- name    : ByzSigT.lemma_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:00:50.235817+00:00
-- url     : https://prove2.me/theorems/cdad448a-ecfe-4b69-997a-8b329030b23c
-- title:
--   Lemma 4.13: valid $V2$ certificates of layer $k+1$ agree
-- statement:
--   Let $k\ge 1$, $f<\frac{2^{k+1}-1}{2^{k+2}-1}n$, $\Delta>0$, and let $E$ be an execution of the $k$-SigT protocol with an $f$-bounded corrupt set $F$ and stabilization time $\mathrm{GST}\ge0$. If $\sigma,\sigma'$ are valid $V2$ certificates of layer $k+1$, of any views, for values $a$ and $b$, and both are present in $E$, then $a=b$.
--
--   Certificates of layer $k+1$ are valid only if they prove more than $(3f-n)/2$ parties corrupt, so two conflicting ones would identify more than $f$ parties. This is the safety of the last layer.
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
--   - reading: “No two valid V2 certificates of layer k + 1” (no existence qualifier) → both certificates are present in E (each exists, or each of its messages exists); reason: the analysis is about the objects of an execution (“Nomenclature”, p.15); for arbitrary terms the conclusion fails, since a term may carry signatures of correct parties that no correct party produced, or two tokens of one corrupt party and index that were never delivered
-- source:
--   Efron, Kelkar, Mutreja, Roughgarden, Byzantine Agreement with Signature Tokens, STOC 2027 submission (manuscript sha256 f020c58a…), Lemma 4.13, p.23 (PDF p.24)

import Mathlib
import Definitions.Def_ByzSigT_ExistsIn

namespace ByzSigT

/-- **Lemma 4.13** (p.23, PDF p.24). Efron, Kelkar, Mutreja, Roughgarden, *Byzantine Agreement with Signature Tokens*, STOC 2027
submission (manuscript sha256 f020c58a…):

> No two valid V2 certificates of layer k + 1 are for different values.

**Formalization Note.** The standing hypotheses are those of the analysis (p.18): `k ≥ 1`,
`f < (2^{k+1}−1)n/(2^{k+2}−1)` (cross-multiplied in `ℕ`), `Δ > 0`, an `f`-bounded corrupt set `F`,
`GST ≥ 0`, and an execution `E` of the k-SigT protocol `kSigT n f k Δ` (Algorithm 1), in which the
input conditions of every layer hold (Lemma 4.23). The certificates are of any views and present in `E`. -/
theorem lemma_4_13 {n f k : ℕ} {Δ GST : ℝ} {F : Finset (Fin n)} {u : Fin n → Bool} {E : Execution n k}
    (hk : 1 ≤ k) (hf : (2 ^ (k + 2) - 1) * f < (2 ^ (k + 1) - 1) * n) (hΔ : 0 < Δ)
    (hF : F.card ≤ f) (hGST : 0 ≤ GST) (hE : IsExecution (kSigT n f k Δ) F u GST Δ E)
    (v w : ℕ) (a b : Bool) (σ σ' : Term n k)
    (hσ : ValidCert f (.V2 v) (k + 1) a σ) (hσ' : ValidCert f (.V2 w) (k + 1) b σ')
    (hσE : Present f Δ F u E σ) (hσE' : Present f Δ F u E σ') : a = b := by sorry

end ByzSigT
