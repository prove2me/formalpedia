-- Prove2me | Theorems.Thm_ByzSigT_lemma_4_9
-- name    : ByzSigT.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:59:45.562467+00:00
-- url     : https://prove2.me/theorems/c64b2f24-44a8-495d-a533-a8422529e85a
-- title:
--   Lemma 4.9: a tally against an allgood certificate exposes many parties
-- statement:
--   Let $k\ge 1$, $f<\frac{2^{k+1}-1}{2^{k+2}-1}n$, $\Delta>0$, and let $E$ be an execution of the $k$-SigT protocol with an $f$-bounded corrupt set $F$ and stabilization time $\mathrm{GST}\ge0$. Let $\sigma$ be a valid allgood certificate for $a$ present in $E$, and let $J$ be a valid tally justification for $b\ne a$ that exists in $E$ and does not use line 56, both from a layer $i$. Then $J$ selects a $V3_b$ certificate $\tau_b$. With $G=\mathrm{signers}(\sigma)$ and $O=\mathrm{equivSenders}(J)$,
--
--   $$|G\cap(\mathrm{signers}(\tau_b)\cup O)|\ge\frac{3n-5f}{2},$$
--
--   and $\sigma$ and $J$ together prove corrupt a set $B$ with $G\cap(\mathrm{signers}(\tau_b)\cup O)\subseteq B\subseteq F$ and
--
--   $$|B|\ge\frac{3n-5f}{2}+|D_\sigma|+|D_{\tau_b}|.$$
--
--   A tally output may differ from a clean output in the same layer, and this lemma shows that the disagreement reveals at least $(3n-5f)/2$ corrupt parties. This is the source of the term $(3n-5f)/2$ in the resilience bound.
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
--   - encoding: bounds with (3n − 5f)/2 → the same bounds multiplied by 2, in ℤ; reason: equivalent, and free of division
--   - reading: “let τ_b be the V3_b certificate selected in J” → that J selects such a certificate is part of the conclusion, and the bounds hold for it; reason: the proof shows V = {a, b} before τ_b is used, so the selection is a consequence, not an extra assumption
--   - reading: “Let σ be an allgood certificate for a, and let J be a valid tally justification for b ≠ a” (no existence qualifier) → σ is a valid allgood certificate present in E (it exists, or each of its messages exists) and J exists in E; reason: the analysis is about the objects of an execution (“Nomenclature”, p.15); for arbitrary terms the conclusion fails, since a term may carry signatures of correct parties that no correct party produced, or two tokens of one corrupt party and index that were never delivered
-- source:
--   Efron, Kelkar, Mutreja, Roughgarden, Byzantine Agreement with Signature Tokens, STOC 2027 submission (manuscript sha256 f020c58a…), Lemma 4.9, p.20 (PDF p.21)

import Mathlib
import Definitions.Def_ByzSigT_ExistsIn

namespace ByzSigT

/-- **Lemma 4.9** (p.20, PDF p.21). Efron, Kelkar, Mutreja, Roughgarden, *Byzantine Agreement with Signature Tokens*, STOC 2027
submission (manuscript sha256 f020c58a…):

> Let σ be an allgood certificate for a, and let J be a valid tally justification for b ≠ a that
> does not use line 56, both from layer i. Let G = signers(σ), let O be the set equivSenders in J,
> and let τ_b be the V3_b certificate selected in J. Then |G ∩ (signers(τ_b) ∪ O)| ≥ (3n − 5f)/2, and
> σ and J together identify a set B with G ∩ (signers(τ_b) ∪ O) ⊆ B ⊆ F such that
> |B| ≥ (3n − 5f)/2 + |D_σ| + |D_τb|.

**Formalization Note.** The standing hypotheses are those of the analysis (p.18): `k ≥ 1`,
`f < (2^{k+1}−1)n/(2^{k+2}−1)` (cross-multiplied in `ℕ`), `Δ > 0`, an `f`-bounded corrupt set `F`,
`GST ≥ 0`, and an execution `E` of the k-SigT protocol `kSigT n f k Δ` (Algorithm 1), in which the
input conditions of every layer hold (Lemma 4.23). `σ` is a valid allgood certificate present in `E` and `J` a valid
justification from layer `i` that exists in `E`. The lemma presupposes that `J` selects a `V3_b`
certificate; that a selection exists is stated as a conclusion. "Identify" is: `B` lies in the
corrupt set of the tuple `⟨σ, J⟩`. The bounds with `(3n − 5f)/2` are doubled, in `ℤ`. -/
theorem lemma_4_9 {n f k : ℕ} {Δ GST : ℝ} {F : Finset (Fin n)} {u : Fin n → Bool} {E : Execution n k}
    (hk : 1 ≤ k) (hf : (2 ^ (k + 2) - 1) * f < (2 ^ (k + 1) - 1) * n) (hΔ : 0 < Δ)
    (hF : F.card ≤ f) (hGST : 0 ≤ GST) (hE : IsExecution (kSigT n f k Δ) F u GST Δ E)
    (i : ℕ) (a b : Bool) (hab : b ≠ a) (σ J : Term n k)
    (hσ : ValidCert f .allgood i a σ) (hσE : Present f Δ F u E σ)
    (hJ : IsJustFrom f J i b) (hJt : JustTypeIs J .tally) (hJE : ExistsIn f Δ F u E J)
    (h56 : ¬ UsesLine56 f J) :
    (∃ τ : Term n k, SelectedV3 J b τ) ∧
    ∀ τb : Term n k, SelectedV3 J b τb →
      3 * (n : ℤ) - 5 * f ≤ 2 * ((certSigners σ ∩ (certSigners τb ∪ equivSenders J)).card : ℤ) ∧
      ∃ B : Finset (Fin n), certSigners σ ∩ (certSigners τb ∪ equivSenders J) ⊆ B ∧ B ⊆ F ∧
        B ⊆ corruptSet f (.list [σ, J]) ∧
        3 * (n : ℤ) - 5 * f + 2 * (corruptSet f σ).card + 2 * (corruptSet f τb).card ≤
          2 * (B.card : ℤ) := by sorry

end ByzSigT
