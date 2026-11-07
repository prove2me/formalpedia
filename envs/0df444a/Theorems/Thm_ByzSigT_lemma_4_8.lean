-- Prove2me | Theorems.Thm_ByzSigT_lemma_4_8
-- name    : ByzSigT.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:59:33.944196+00:00
-- url     : https://prove2.me/theorems/4bc2a506-cdc5-4b26-8831-3c0428c14dbd
-- title:
--   Lemma 4.8: certificates and justifications carry their history
-- statement:
--   Let $k\ge 1$, $f<\frac{2^{k+1}-1}{2^{k+2}-1}n$, $\Delta>0$, and let $E$ be an execution of the $k$-SigT protocol with an $f$-bounded corrupt set $F$ and stabilization time $\mathrm{GST}\ge0$. Let $X$ be a valid certificate for $a$ of layer $m\le k$, or a valid justification for $a$ from layer $m<k$.
--
--   1. For every layer $j$ with $1\le j<m$, $X$ contains a justification for $a$ from layer $j$.
--   2. If $X$ is present in $E$ and an allgood certificate from such a layer $j$ for a value other than $a$ exists in $E$, then every justification for $a$ from layer $j$ in $X$ is of type tally.
--   3. If $X$ contains an adopt or tally justification from layer $m-1$ and no allgood certificate from a layer before $m-1$, then
--
--   $$|D_X|\ge T_m .$$
--
--   This is how layers compound: as long as no allgood certificate forms, the number of parties proved corrupt inside a certificate grows as $T_i=(2^{i-1}-1)(n-2f)$.
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
--   - reading: “there exists an allgood certificate”; layers j < m → existence in E (p.15), with X itself present in E; layers are at least 1; reason: the paper defines existence for executions, and layers are numbered from 1
--   - reading: “a certificate exists” (p.15 defines existence for messages only) → every message of the certificate exists in E (`CertExists`), possibly received by different correct parties; reason: a certificate is a set of messages, and the paper defines existence for messages; every certificate some correct party receives counts
-- source:
--   Efron, Kelkar, Mutreja, Roughgarden, Byzantine Agreement with Signature Tokens, STOC 2027 submission (manuscript sha256 f020c58a…), Lemma 4.8, p.19 (PDF p.20)

import Mathlib
import Definitions.Def_ByzSigT_ExistsIn

namespace ByzSigT

/-- **Lemma 4.8** (p.19, PDF p.20). Efron, Kelkar, Mutreja, Roughgarden, *Byzantine Agreement with Signature Tokens*, STOC 2027
submission (manuscript sha256 f020c58a…):

> Let X be a valid certificate for a of layer m ≤ k, or a valid justification for a from layer
> m < k.
> 1. For every j < m, X contains a justification for a from layer j. If there exists an allgood
>    certificate from layer j for a value other than a, every justification for a from layer j in X
>    is of type tally.
> 2. If X contains an adopt or tally justification from layer m − 1 and no allgood certificate from
>    a layer before m − 1, then |D_X| ≥ T_m.

**Formalization Note.** The standing hypotheses are those of the analysis (p.18): `k ≥ 1`,
`f < (2^{k+1}−1)n/(2^{k+2}−1)` (cross-multiplied in `ℕ`), `Δ > 0`, an `f`-bounded corrupt set `F`,
`GST ≥ 0`, and an execution `E` of the k-SigT protocol `kSigT n f k Δ` (Algorithm 1), in which the
input conditions of every layer hold (Lemma 4.23). Layers are `≥ 1`, so "every j < m" is `1 ≤ j < m` and "a layer
before m − 1" is `1 ≤ j < m − 1`. The first sentence and part 2 are syntactic; the second sentence
speaks of objects of `E`, so it is stated for `X` present in `E` ("there exists" is existence in `E`,
p.15). Justifications in `X` are the valid ones occurring in `X`, of any party. `T_m` and `|D_X|`
are compared in `ℤ`. -/
theorem lemma_4_8 {n f k : ℕ} {Δ GST : ℝ} {F : Finset (Fin n)} {u : Fin n → Bool} {E : Execution n k}
    (hk : 1 ≤ k) (hf : (2 ^ (k + 2) - 1) * f < (2 ^ (k + 1) - 1) * n) (hΔ : 0 < Δ)
    (hF : F.card ≤ f) (hGST : 0 ≤ GST) (hE : IsExecution (kSigT n f k Δ) F u GST Δ E)
    (m : ℕ) (a : Bool) (X : Term n k)
    (hX : (∃ κ : CertKind, ValidCert f κ m a X ∧ m ≤ k) ∨ (IsJustFrom f X m a ∧ m < k)) :
    (∀ j, 1 ≤ j → j < m → ∃ J : Term n k, Term.Subterm J X ∧ IsJustFrom f J j a) ∧
    (Present f Δ F u E X → ∀ j, 1 ≤ j → j < m → ∀ b : Bool, b ≠ a →
      CertExists f Δ F u E .allgood j b →
        ∀ J : Term n k, Term.Subterm J X → IsJustFrom f J j a → JustTypeIs J .tally) ∧
    ((∃ (J : Term n k) (b : Bool), Term.Subterm J X ∧ IsJustFrom f J (m - 1) b ∧
        (JustTypeIs J .adopt ∨ JustTypeIs J .tally)) →
      (¬ ∃ (j : ℕ) (b : Bool), 1 ≤ j ∧ j < m - 1 ∧ ContainsAllgood f X j b) →
        T n f m ≤ ((corruptSet f X).card : ℤ)) := by sorry

end ByzSigT
