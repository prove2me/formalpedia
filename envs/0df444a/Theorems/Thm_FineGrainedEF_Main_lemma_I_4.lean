-- Prove2me | Theorems.Thm_FineGrainedEF_Main_lemma_I_4
-- name    : FineGrainedEF.Main.lemma_I_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:13:42.537201+00:00
-- url     : https://prove2.me/theorems/1f8da957-86db-40c1-9247-c3e9d6572f05
-- title:
--   Lemma I.4 — zero-padding: Pad_N(FFTMul_{r,s}(x, y)) equals the full carry array Carry(FFTConv_round(a, b))
-- statement:
--   For $n\ge1$ let $N,L$ be the multiplier's parameters. Let $\Gamma$ be well formed and $x\in\{0,1\}^r$, $y\in\{0,1\}^s$ words of $\Gamma$ with $r,s\ge1$ and $\ell:=r+s+L+2<N$; let $a,b$ be their length-$N$ bit embeddings. There are $C,k$ such that
--   $$\Gamma\ \triangleright^{C N L^k}_{\mathrm{EF}}\ \mathrm{Pad}_N(\mathrm{FFTMul}_{r,s}(x,y))=\mathrm{Carry}(\mathrm{FFTConv}_{\mathrm{round}}(a,b)),$$
--   where $\mathrm{FFTMul}_{r,s}(x,y)$ is the first $\ell$ bits of that same carry circuit. The multiplier's declared output thus loses no nonzero bit.
--
--   Differences from the source:
--   - reading: a sound and implicationally complete finite set of rules, formulas over arbitrary unary or binary Boolean operators (p. 4) → the printed AX1–AX3 and modus ponens in circuit form (letters = wires, connectives = gates of the context) plus the axiom ⊤ for a constant-true gate; gate basis {⊤, ¬, →}, with ∧, ∨, ↔, ⊕ fixed 2–6-gate sub-circuits; reason: the paper fixes one such set and notes that the choice of operators and axiom schemes does not affect asymptotic size (footnote 1, p. 4)
--   - encoding: contexts of inputs, gate definitions and assertions; expanded context Γ ∪ Φ; circuits and premises supplied in Γ → Ctx = indexed wire list + assertion list; conclusion circuits appended by Build.expand; Contains maps a generated circuit into existing gates, fixing its input wires and preserving operators and edges; Asserts requires a contained check with asserted output; reason: structural wire mapping allows arbitrary surrounding circuitry, interleaving and shared gates, as required by Section 2.2; no contiguity assumption is imposed
--   - reading: O(f) cost of a family of big-step rules (p. 8) → one existential constant chosen before every universally quantified parameter, context and wire; reason: the paper: a family with cost O(f) has one constant for the whole family and every Γ meeting the requirements
--   - encoding: N, L of the multiplier fixed by n (p. 48), lemma stated for the multiplier's N → N, L of paperParams n, for every n ≥ 1; reason: the lemmas of Appendices G–I are used at exactly these parameters
--   - encoding: cost N log^{O(1)} N → C·N·L^k with L = log₂ N; reason: N = 2^L
-- source:
--   Krapivin, Li, Shi, Fine-Grained Proof Complexity for Elementary Arithmetic in Extended Frege, STOC 2027 submission (manuscript sha256 704dfb8a…), p. 133, Lemma I.4

import Mathlib
import Definitions.Def_FineGrainedEF_Main_EF
import Definitions.Def_FineGrainedEF_Main_BoolCircuits
import Definitions.Def_FineGrainedEF_Main_IntCircuits
import Definitions.Def_FineGrainedEF_Main_ScaledArith
import Definitions.Def_FineGrainedEF_Main_FFTMul
import Definitions.Def_FineGrainedEF_Main_Checks

namespace FineGrainedEF.Main

/-- Lemma I.4 (Zero-padding the multiplier output), p. 133. There are `C, k` such that, for every
`n ≥ 1`, every well-formed `Γ` and all input words `x ∈ {0,1}^r`, `y ∈ {0,1}^s` of `Γ` with
`r, s ≥ 1` and `ℓ := r + s + L + 2 < N`: with `a, b` the length-`N` bit embeddings of `x, y`,
`Γ ▷^{C·N·L^k} Pad_N(FFTMul_{r,s}(x, y)) = Carry(FFTConv_round(a, b))`, where `FFTMul_{r,s}(x, y)`
is the first `ℓ` output bits of the same carry circuit. -/
theorem lemma_I_4 :
    ∃ C k : ℕ, ∀ (n : ℕ) (Γ : Ctx) (x y : List ℕ),
      1 ≤ n → Γ.WF → 1 ≤ x.length → 1 ≤ y.length →
      x.length + y.length + (paperParams n).L + 2 < (paperParams n).N →
      Γ.HasWires (x ++ y) →
      BigStep Γ
        (do let r ← fftMulFull (paperParams n) x y
            let m := r.1.take (x.length + y.length + (paperParams n).L + 2)
            let p ← pad (paperParams n).N m
            let e ← eqBits p r.1
            pure [e])
        (C * (paperParams n).N * (paperParams n).L ^ k) := by sorry

end FineGrainedEF.Main
