-- Prove2me | Theorems.Thm_ByzSigT_lemma_4_11
-- name    : ByzSigT.lemma_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:59:56.740712+00:00
-- url     : https://prove2.me/theorems/3cf469d6-cd0b-4fad-8177-4f0be8b1134e
-- title:
--   Lemma 4.11: what conflicting certificates identify
-- statement:
--   Let $k\ge 1$, $f<\frac{2^{k+1}-1}{2^{k+2}-1}n$, $\Delta>0$, and let $E$ be an execution of the $k$-SigT protocol with an $f$-bounded corrupt set $F$ and stabilization time $\mathrm{GST}\ge0$. Let $1\le i\le k$.
--
--   1. Conflicting certificates of layer $i$ present in $E$ together prove corrupt a set $B\subseteq F$ with
--
--   $$|B|\ge\min\Bigl\{\frac{3n-5f}{2},\,T_{i+1}\Bigr\},$$
--
--   and if $7f<3n+4T_i$, then $3(f-|B|)<n-|B|$.
--
--   2. Every correct party that outputs adopt or tally in layer $i$ has such a set in its blame at its output.
--
--   The inequality $3(f-|B|)<n-|B|$ says that after removing $B$, fewer than a third of the remaining parties are corrupt, which is the condition layer $k+1$ needs.
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
--   - encoding: the bound min{(3n − 5f)/2, T_{i+1}} → min{3n − 5f, 2T_{i+1}} ≤ 2|B| in ℤ; reason: equivalent, and free of division
--   - reading: “has such a set in blame at its output” → a set B ⊆ F with both properties inside the corrupt set of the blame recorded with the output; reason: blame is the set of parties proved corrupt by the stored evidence (p.15)
--   - reading: “Conflicting certificates of layer i ≤ k” (no existence qualifier) → both certificates are present in E (each exists, or each of its messages exists); reason: the analysis is about the objects of an execution (“Nomenclature”, p.15); for arbitrary terms the conclusion fails, since a term may carry signatures of correct parties that no correct party produced, or two tokens of one corrupt party and index that were never delivered
-- source:
--   Efron, Kelkar, Mutreja, Roughgarden, Byzantine Agreement with Signature Tokens, STOC 2027 submission (manuscript sha256 f020c58a…), Lemma 4.11, p.21 (PDF p.22)

import Mathlib
import Definitions.Def_ByzSigT_ExistsIn

namespace ByzSigT

/-- **Lemma 4.11** (p.21, PDF p.22). Efron, Kelkar, Mutreja, Roughgarden, *Byzantine Agreement with Signature Tokens*, STOC 2027
submission (manuscript sha256 f020c58a…):

> Conflicting certificates of layer i ≤ k identify a set B ⊆ F with
> |B| ≥ min{(3n − 5f)/2, T_{i+1}}. If 7f < 3n + 4T_i, then 3(f − |B|) < n − |B|. Every correct party
> that outputs adopt or tally in layer i has such a set in blame at its output.

**Formalization Note.** The standing hypotheses are those of the analysis (p.18): `k ≥ 1`,
`f < (2^{k+1}−1)n/(2^{k+2}−1)` (cross-multiplied in `ℕ`), `Δ > 0`, an `f`-bounded corrupt set `F`,
`GST ≥ 0`, and an execution `E` of the k-SigT protocol `kSigT n f k Δ` (Algorithm 1), in which the
input conditions of every layer hold (Lemma 4.23). Layers are `≥ 1`. The certificates are present in `E`; "identify"
is: `B` lies in the corrupt set of the pair. The second clause is for the same `B`. "Such a set" is
a `B ⊆ F` with both properties, inside the party's blame at its output (the corrupt set of the
blame tuple recorded with the output). The bound `min{(3n − 5f)/2, T_{i+1}}` is doubled, in `ℤ`. -/
theorem lemma_4_11 {n f k : ℕ} {Δ GST : ℝ} {F : Finset (Fin n)} {u : Fin n → Bool} {E : Execution n k}
    (hk : 1 ≤ k) (hf : (2 ^ (k + 2) - 1) * f < (2 ^ (k + 1) - 1) * n) (hΔ : 0 < Δ)
    (hF : F.card ≤ f) (hGST : 0 ≤ GST) (hE : IsExecution (kSigT n f k Δ) F u GST Δ E)
    (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) :
    (∀ σa σb : Term n k, Conflicting f i σa σb → Present f Δ F u E σa → Present f Δ F u E σb →
      ∃ B : Finset (Fin n), B ⊆ corruptSet f (.list [σa, σb]) ∧ B ⊆ F ∧
        min (3 * (n : ℤ) - 5 * f) (2 * T n f (i + 1)) ≤ 2 * (B.card : ℤ) ∧
        (7 * (f : ℤ) < 3 * n + 4 * T n f i → 3 * ((f : ℤ) - B.card) < (n : ℤ) - B.card)) ∧
    (∀ p ∉ F, ∀ r : OutRec n k, OutputRec f Δ u E p r → r.layer = i → r.type ≠ .clean →
      ∃ B : Finset (Fin n), B ⊆ corruptSet f r.blame ∧ B ⊆ F ∧
        min (3 * (n : ℤ) - 5 * f) (2 * T n f (i + 1)) ≤ 2 * (B.card : ℤ) ∧
        (7 * (f : ℤ) < 3 * n + 4 * T n f i → 3 * ((f : ℤ) - B.card) < (n : ℤ) - B.card)) := by sorry

end ByzSigT
