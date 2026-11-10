-- Prove2me | Theorems.Thm_FineGrainedEF_Main_lemma_B_4
-- name    : FineGrainedEF.Main.lemma_B_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:09:48.356846+00:00
-- url     : https://prove2.me/theorems/3e8bb11d-abb2-4e89-bbac-e748a39af23d
-- title:
--   Lemma B.4 — equality propagation and substitution through a circuit, conditional and bitwise forms, symmetry and transitivity of EQ
-- statement:
--   Let $\Gamma$ be well formed, $x,y,u$ $w$-bit strings of wires of $\Gamma$ ($w\ge1$), $z$ further wires, $H$ a wire, and $C$ a Boolean circuit on $w+|z|$ inputs with $r\ge1$ outputs and $|C|$ gates; $C(x,z)$ and $C(y,z)$ are copies of the same gate structure sharing $z$. There is one constant $K$ such that, for all such data,
--   $$\Gamma:\mathrm{EQ}(x,y)\ \triangleright^{K(w+|C|+r)}\ \mathrm{EQ}(C(x,z),C(y,z))\ \ (50),\qquad \Gamma:H\to\mathrm{EQ}(x,y)\ \triangleright^{K(w+|C|+r)}\ H\to\mathrm{EQ}(C(x,z),C(y,z))\ \ (51);$$
--   for a single-output $P$: $\Gamma:\mathrm{EQ}(x,y),P(x,z)\triangleright^{K(w+|P|)}P(y,z)$ (52) and $\Gamma:H\to\mathrm{EQ}(x,y),H\to P(x,z)\triangleright^{K(w+|P|)}H\to P(y,z)$ (53); bitwise, $\Gamma:[H\to(x_t\leftrightarrow y_t)]_{t<w}\triangleright^{K(|C|+r)}H\to\mathrm{EQ}(C(x,z),C(y,z))$ (54) and the same without $H$; and
--   $$\Gamma:\mathrm{EQ}(x,y)\ \triangleright^{Kw}\ \mathrm{EQ}(y,x),\qquad \Gamma:\mathrm{EQ}(x,y),\mathrm{EQ}(y,u)\ \triangleright^{Kw}\ \mathrm{EQ}(x,u)\ \ (55),$$
--   also with a common antecedent $H$ on every premise and the conclusion. $|C|$ counts only $C$'s own gates. Equality propagation is the workhorse that transports identities through circuits.
--
--   Differences from the source:
--   - reading: a sound and implicationally complete finite set of rules, formulas over arbitrary unary or binary Boolean operators (p. 4) → the printed AX1–AX3 and modus ponens in circuit form (letters = wires, connectives = gates of the context) plus the axiom ⊤ for a constant-true gate; gate basis {⊤, ¬, →}, with ∧, ∨, ↔, ⊕ fixed 2–6-gate sub-circuits; reason: the paper fixes one such set and notes that the choice of operators and axiom schemes does not affect asymptotic size (footnote 1, p. 4)
--   - encoding: contexts of inputs, gate definitions and assertions; expanded context Γ ∪ Φ; circuits and premises supplied in Γ → Ctx = indexed wire list + assertion list; conclusion circuits appended by Build.expand; Contains maps a generated circuit into existing gates, fixing its input wires and preserving operators and edges; Asserts requires a contained check with asserted output; reason: structural wire mapping allows arbitrary surrounding circuitry, interleaving and shared gates, as required by Section 2.2; no contiguity assumption is imposed
--   - reading: O(f) cost of a family of big-step rules (p. 8) → one existential constant chosen before every universally quantified parameter, context and wire; reason: the paper: a family with cost O(f) has one constant for the whole family and every Γ meeting the requirements
--   - encoding: C a Boolean circuit with |C| gates; copies C(x, z), C(y, z) of the same gate structure → an abstract well-formed Circuit over the pinned basis, instantiated by Circuit.apply on x ++ z and y ++ z; the copies are conclusion circuits; reason: the copies share the gate structure by construction; the gate basis is the pinned one
-- source:
--   Krapivin, Li, Shi, Fine-Grained Proof Complexity for Elementary Arithmetic in Extended Frege, STOC 2027 submission (manuscript sha256 704dfb8a…), p. 57, Lemma B.4 (50)-(55)

import Mathlib
import Definitions.Def_FineGrainedEF_Main_EF
import Definitions.Def_FineGrainedEF_Main_BoolCircuits

namespace FineGrainedEF.Main

/-- Lemma B.4 (Equality propagation and substitution), p. 57. One constant `K` for the whole
family: every well-formed `Γ`, all `w`-bit strings `x, y, u` of `Γ` (`w ≥ 1`), every list `z` of
further wires of `Γ`, every wire `H`, and every well-formed abstract circuit `C` on `w + |z|`
inputs with `r ≥ 1` outputs (`|C|` its gates). The copies `C(x, z)`, `C(y, z)` are instantiated in
the conclusion. Clauses: (50), (51), (52), (53) (for `C` with one output, `P = C`), (54) with and
without the antecedent `H`, and (55) symmetry and transitivity, unconditional and with a common
antecedent `H`. -/
theorem lemma_B_4 :
    ∃ K : ℕ, ∀ (Γ : Ctx) (H : ℕ) (x y u z : List ℕ) (C : Circuit),
      Γ.WF → 1 ≤ x.length → y.length = x.length → u.length = x.length →
      Γ.HasWires (H :: (x ++ y ++ u ++ z)) → C.WF → C.nIn = x.length + z.length →
      1 ≤ C.outs.length →
      -- (50)
      (Asserts Γ (eqBits x y) →
          BigStep Γ (do let cx ← C.apply (x ++ z); let cy ← C.apply (y ++ z);
                        let e ← eqBits cx cy; pure [e])
            (K * (x.length + C.size + C.outs.length))) ∧
      -- (51)
      (Asserts Γ (do let e ← eqBits x y; impG H e) →
          BigStep Γ (do let cx ← C.apply (x ++ z); let cy ← C.apply (y ++ z);
                        let e ← eqBits cx cy; let h ← impG H e; pure [h])
            (K * (x.length + C.size + C.outs.length))) ∧
      -- (52)
      (C.outs.length = 1 → Asserts Γ (eqBits x y) →
          Asserts Γ (do let o ← C.apply (x ++ z); pure (o.headD 0)) →
          BigStep Γ (C.apply (y ++ z)) (K * (x.length + C.size))) ∧
      -- (53)
      (C.outs.length = 1 → Asserts Γ (do let e ← eqBits x y; impG H e) →
          Asserts Γ (do let o ← C.apply (x ++ z); impG H (o.headD 0)) →
          BigStep Γ (do let o ← C.apply (y ++ z); let h ← impG H (o.headD 0); pure [h])
            (K * (x.length + C.size))) ∧
      -- (54), conditional
      ((∀ i < x.length, Asserts Γ (do let e ← iffG (x.getD i 0) (y.getD i 0); impG H e)) →
          BigStep Γ (do let cx ← C.apply (x ++ z); let cy ← C.apply (y ++ z);
                        let e ← eqBits cx cy; let h ← impG H e; pure [h])
            (K * (C.size + C.outs.length))) ∧
      -- (54), without the antecedent
      ((∀ i < x.length, Asserts Γ (iffG (x.getD i 0) (y.getD i 0))) →
          BigStep Γ (do let cx ← C.apply (x ++ z); let cy ← C.apply (y ++ z);
                        let e ← eqBits cx cy; pure [e])
            (K * (C.size + C.outs.length))) ∧
      -- (55), symmetry and transitivity
      (Asserts Γ (eqBits x y) →
          BigStep Γ (do let e ← eqBits y x; pure [e]) (K * x.length)) ∧
      (Asserts Γ (eqBits x y) → Asserts Γ (eqBits y u) →
          BigStep Γ (do let e ← eqBits x u; pure [e]) (K * x.length)) ∧
      -- (55), conditional forms
      (Asserts Γ (do let e ← eqBits x y; impG H e) →
          BigStep Γ (do let e ← eqBits y x; let h ← impG H e; pure [h]) (K * x.length)) ∧
      (Asserts Γ (do let e ← eqBits x y; impG H e) → Asserts Γ (do let e ← eqBits y u; impG H e) →
          BigStep Γ (do let e ← eqBits x u; let h ← impG H e; pure [h]) (K * x.length)) := by sorry

end FineGrainedEF.Main
