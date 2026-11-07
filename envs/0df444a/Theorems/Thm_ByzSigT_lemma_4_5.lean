-- Prove2me | Theorems.Thm_ByzSigT_lemma_4_5
-- name    : ByzSigT.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:59:24.8642+00:00
-- url     : https://prove2.me/theorems/975dea99-e0a7-4918-b231-3db37ac8e27d
-- title:
--   Lemma 4.5: $V2$ certificates for different values contain conflicting certificates
-- statement:
--   Let $\sigma_a,\sigma_b$ be valid $V2$ certificates of a layer $i$ for values $a\ne b$ and of views $w\le w'$ respectively. Then some certificate occurring in $\sigma_a$ and some certificate occurring in $\sigma_b$ are conflicting.
--
--   The statement is about the syntax of valid terms and needs no execution. It reduces safety of the view stage to the existence of conflicting certificates: two different values cannot both reach a $V2$ certificate unless a proof of equivocation appears.
--
--   Differences from the source:
--   - generalization: “n is such that all fractions we consider are integers” (p.4) → no divisibility hypothesis on n and f; every comparison with a fraction is made in ℤ; reason: the fractions occur only inside inequalities, each step of the proof holds over ℚ, and the printed case is the instance where the fractions are integers
--   - encoding: f < (2^{k+1}−1)n/(2^{k+2}−1) → (2^{k+2}−1)·f < (2^{k+1}−1)·n in ℕ; reason: cross-multiplied by a positive number; the same pairs (n, f)
--   - reading: “σ_a and σ_b contain conflicting certificates” → one of the two conflicting certificates occurs in σ_a and the other in σ_b; reason: the proof's cases all have this form, and this implies the reading in which both occur somewhere in the pair
-- source:
--   Efron, Kelkar, Mutreja, Roughgarden, Byzantine Agreement with Signature Tokens, STOC 2027 submission (manuscript sha256 f020c58a…), Lemma 4.5, p.19 (PDF p.20)

import Mathlib
import Definitions.Def_ByzSigT_ExistsIn

namespace ByzSigT

/-- **Lemma 4.5** (p.19, PDF p.20). Efron, Kelkar, Mutreja, Roughgarden, *Byzantine Agreement with Signature Tokens*, STOC 2027
submission (manuscript sha256 f020c58a…):

> Let σ_a, σ_b be valid V2 certificates of layer i for values a ≠ b and views w ≤ w′, respectively.
> Then σ_a and σ_b contain conflicting certificates.

**Formalization Note.** A statement about certificates alone (no execution), under the arithmetic
standing hypotheses of p.18 (`k ≥ 1` and the bound on `f`). "σ_a and σ_b contain conflicting
certificates" is read as one certificate in each: `τ` occurs in `σ_a` and `τ'` in `σ_b` (the proof's
three cases are of this form); this implies the reading "both inside the pair". -/
theorem lemma_4_5 {n f k : ℕ} (hk : 1 ≤ k) (hf : (2 ^ (k + 2) - 1) * f < (2 ^ (k + 1) - 1) * n)
    (i w w' : ℕ) (a b : Bool) (hab : a ≠ b) (hww : w ≤ w') (σa σb : Term n k)
    (ha : ValidCert f (.V2 w) i a σa) (hb : ValidCert f (.V2 w') i b σb) :
    ∃ τ τ' : Term n k, Term.Subterm τ σa ∧ Term.Subterm τ' σb ∧ Conflicting f i τ τ' := by sorry

end ByzSigT
