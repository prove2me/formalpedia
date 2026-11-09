-- Prove2me | Theorems.Thm_EditMulticoloring_Code_explicit_edit_codes
-- name    : EditMulticoloring.Code.explicit_edit_codes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T18:50:46.658905+00:00
-- url     : https://prove2.me/theorems/26b8e2eb-999b-4284-b881-3920658f79f4
-- title:
--   Theorem 1 — Explicit mixed-edit codes at the leading redundancy term
-- statement:
--   For every fixed integer alphabet size $q\ge2$ and edit budget $t\ge1$, there are fixed finite deterministic encoder and decoder programs, uniform positive constants $C,C_E,C_D$, natural exponents $d_E,d_D$, and a threshold $n_0\ge3$. For every $n\ge n_0$, the parameterized construction chooses a valid binary polynomial-basis field representation internally, has positive prefix length, and encodes every message in $A^{k(n)}$ injectively into $A^n$, with
--
--   $$k(n)\ge n-2t\log_qn-C\log\log n.$$
--
--   Its image corrects every combination of at most $t$ insertions, deletions and substitutions. For every message, an actual halting encoder execution produces that codeword with cost at most
--
--   $$C_E n^{6t+2}(1+\log n)^{d_E}.$$
--
--   For every finite received word, an actual halting decoder execution produces the defined decoder result with cost at most
--
--   $$C_D n^{7t+2}(1+\log n)^{d_D}.$$
--
--   The decoder returns a given message exactly when the received word is within $t$ edits of its codeword, and rejects exactly when no message has such a codeword. Each execution starts with zero working memory and no public tables, so field construction, prime setup, short-code table construction, conversion, input access and output writing are all included. The internal modulus family is not an input or a free computational oracle: validity and realization by the fixed finite programs are conclusions. The decoder may inspect only a bounded prefix before rejecting overlong inputs, as in Appendix D.3. Constants and exponents are chosen before $n$ and before inputs.
--
--   Differences from the source:
--   - encoding: finite words over an alphabet of q symbols and one-based positions → lists of Fin q, finite-coordinate functions for fixed lengths, and zero-based stored operations; reason: order-preserving conversion and the explicit interval formula preserve every source word and positioned edit
--   - encoding: O and soft-O with constants depending on fixed q,t → positive uniform constants, natural polylog exponents and thresholds quantified before lengths and inputs; reason: this expands the source asymptotic conventions without changing the leading term or either runtime exponent
--   - encoding: the finite field of order Q with a chosen binary polynomial-basis representation → bit-mask polynomial arithmetic modulo any monic irreducible polynomial of degree log2 Q; reason: these are the coefficient-vector labels of Appendix D.1; the goal concludes validity and operational realization rather than assuming a free field oracle
--   - encoding: deterministic random-access algorithms charged by bit complexity and address length → finite instruction lists with schoolbook bit charges and explicit input/output transitions; reason: programs have operational executions; setup is included from empty working memory, and received input is available before bounded inspection as in Appendix D.3
--   - encoding: return the recovered message or reject the received word → Option of a word, with some u for message u and none for rejection; reason: this represents the two source outcomes explicitly and preserves recovery and exact rejection on every finite received word
-- source:
--   Huiling Xie, Zitan Chen, Explicit Edit Codes via Multicoloring, STOC 2027 submission #819 (October 2026), Theorem 1, printed p. 1 (PDF p. 2); Construction 3.1, Lemmas 11–12, printed pp. 10–12 (PDF pp. 11–13); Appendix D, Eqs. (15)–(23), printed pp. 17–21 (PDF pp. 18–22); pinned repository artifact papers/stoc2027-819/source.pdf, SHA256 00172d5da76bf6bc886b8a1f87450befb76480107f54cb367988a065737eb376.

import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine

namespace EditMulticoloring.Code

/-- Theorem 1. Programs are fixed before n; costs are generated only by RAM.step.
The existential modulus family is internal implementation data, never supplied as an oracle.
All setup must occur in the executions starting from RAM.initial n. -/
theorem explicit_edit_codes (q t : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t) :
    ∃ (encoder decoder : RAM.Program) (modulus : ℕ → ℕ)
      (C CE CD : ℝ) (dE dD n₀ : ℕ),
      0 < C ∧ 0 < CE ∧ 0 < CD ∧ 3 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n →
        let P := parameters q t n
        let p := modulus n
        1 ≤ P.m ∧ P.m + P.ρ = n ∧
        ValidModulus (ceilLog 2 (P.r * P.K + 1)) p ∧
        ((P.k : ℝ) ≥ (n : ℝ) - (2 * t : ℕ) * logBase q n -
          C * Real.log (Real.log (n : ℝ))) ∧
        (∀ u : FixedWord q P.k, (encode t n p (toWord u)).length = n) ∧
        Function.Injective (fun u : FixedWord q P.k => encode t n p (toWord u)) ∧
        Corrects t (Set.range (fun u : FixedWord q P.k => encode t n p (toWord u))) ∧
        (∀ u : FixedWord q P.k,
          RAM.Executes encoder n (toWord u)
            (some ((encode t n p (toWord u)).map Fin.val))
            (softBound CE (6 * t + 2) dE n)) ∧
        (∀ y : Word q,
          RAM.Executes decoder n y ((decode t n p y).map (List.map Fin.val))
            (softBound CD (7 * t + 2) dD n)) ∧
        (∀ (u : FixedWord q P.k) (y : Word q),
          decode t n p y = some (toWord u) ↔ distance y (encode t n p (toWord u)) ≤ t) ∧
        (∀ y : Word q, decode t n p y = none ↔
          ∀ u : FixedWord q P.k, t < distance y (encode t n p (toWord u)))
    := by sorry

end EditMulticoloring.Code
