-- Prove2me | Theorems.Thm_FineGrainedEF_Main_lemma_B_5
-- name    : FineGrainedEF.Main.lemma_B_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:09:37.193577+00:00
-- url     : https://prove2.me/theorems/3b898c46-6e69-4958-8800-5f8b8337a5ca
-- title:
--   Lemma B.5 — proof by enumeration over all 2^s values of an s-bit address, cost O(m log(m+1))
-- statement:
--   Let $\Gamma$ be well formed, $s\ge1$, $m=2^s$, $a$ an $s$-bit address of wires of $\Gamma$ and $c$ a wire of $\Gamma$. Write $[a=j]$ for $\mathrm{EQ}(a,\mathrm{enc}_s(j))$, the equality check against the hardwired $s$-bit encoding of $j$. There is one constant $K$ such that for all such data
--   $$\Gamma\ \triangleright^{K\,m\,\lfloor\log_2(m+1)\rfloor}_{\mathrm{EF}}\ \bigvee_{j<m}[a=j]\quad(56),\qquad \Gamma:([a=j]\to c)_{j<m}\ \triangleright^{K\,m\,\lfloor\log_2(m+1)\rfloor}_{\mathrm{EF}}\ c\quad(57).$$
--   Enumeration lets a derivation do a case analysis on the value of an address, each case being proved separately.
--
--   Differences from the source:
--   - reading: a sound and implicationally complete finite set of rules, formulas over arbitrary unary or binary Boolean operators (p. 4) → the printed AX1–AX3 and modus ponens in circuit form (letters = wires, connectives = gates of the context) plus the axiom ⊤ for a constant-true gate; gate basis {⊤, ¬, →}, with ∧, ∨, ↔, ⊕ fixed 2–6-gate sub-circuits; reason: the paper fixes one such set and notes that the choice of operators and axiom schemes does not affect asymptotic size (footnote 1, p. 4)
--   - encoding: contexts of inputs, gate definitions and assertions; expanded context Γ ∪ Φ; circuits and premises supplied in Γ → Ctx = indexed wire list + assertion list; conclusion circuits appended by Build.expand; Contains maps a generated circuit into existing gates, fixing its input wires and preserving operators and edges; Asserts requires a contained check with asserted output; reason: structural wire mapping allows arbitrary surrounding circuitry, interleaving and shared gates, as required by Section 2.2; no contiguity assumption is imposed
--   - reading: O(f) cost of a family of big-step rules (p. 8) → one existential constant chosen before every universally quantified parameter, context and wire; reason: the paper: a family with cost O(f) has one constant for the whole family and every Γ meeting the requirements
--   - encoding: O(m log(m+1)) with the real logarithm → K·m·⌊log₂(m+1)⌋; reason: ⌊log₂(m+1)⌋ = s ≥ 1 is within a factor 2 of log₂(m+1) for m ≥ 2, so the two O-classes coincide
-- source:
--   Krapivin, Li, Shi, Fine-Grained Proof Complexity for Elementary Arithmetic in Extended Frege, STOC 2027 submission (manuscript sha256 704dfb8a…), p. 58, Lemma B.5 (56)-(57)

import Mathlib
import Definitions.Def_FineGrainedEF_Main_EF
import Definitions.Def_FineGrainedEF_Main_BoolCircuits

namespace FineGrainedEF.Main

/-- Lemma B.5 (Proof by enumeration), p. 58. One constant `K` for the whole family: every
well-formed `Γ`, every `s ≥ 1` (`m = 2^s`), every `s`-bit address `a` of `Γ` and every wire `c`
of `Γ`. `[a = j]` is `EQ(a, enc_s(j))` against the hardwired `s`-bit encoding of `j`.
(56) `Γ ▷^{O(m log(m+1))} ⋁_{j<m} [a = j]`;
(57) `Γ : ([a = j] → c)_{j<m} ▷^{O(m log(m+1))} c`. -/
theorem lemma_B_5 :
    ∃ K : ℕ, ∀ (Γ : Ctx) (s : ℕ) (a : List ℕ) (c : ℕ), Γ.WF → 1 ≤ s → a.length = s →
      Γ.HasWires (c :: a) →
      BigStep Γ
          (do let es ← (List.range (2 ^ s)).mapM fun j => do
                let e ← encAddr s j
                eqBits a e
              let t ← orTree es
              pure [t])
          (K * 2 ^ s * Nat.log 2 (2 ^ s + 1)) ∧
      ((∀ j < 2 ^ s, Asserts Γ (do let e ← encAddr s j; let q ← eqBits a e; impG q c)) →
          BigStep Γ (pure [c]) (K * 2 ^ s * Nat.log 2 (2 ^ s + 1))) := by sorry

end FineGrainedEF.Main
