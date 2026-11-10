-- Prove2me | Theorems.Thm_FineGrainedEF_Main_lemma_H_1
-- name    : FineGrainedEF.Main.lemma_H_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:13:25.093252+00:00
-- url     : https://prove2.me/theorems/9898ade8-0dd6-4785-a528-83e0a6883e5b
-- title:
--   Lemma H.1 — exact identities of the rounded FFT convolution: linearity, symmetry, doubling, negation, cyclic shift, associativity
-- statement:
--   Fix a width constant $c_w$. For $n\ge1$ let $N,L$ be the multiplier's parameters, $W=(L+1)^4$, $M=N^8$. Let $\Gamma$ be well formed and $a,b,c$ length-$N$ arrays of signed scale-zero words of $\Gamma$ of width at most $c_wW$. There are $C,k$ (depending only on $c_w$) such that each identity below is derived at cost $C\,N\,L^k$ from the bounds $\|h\|_\infty\le M$ on exactly the arrays $h$ that are inputs of a rounded convolution in that identity (inner outputs included; computed inputs such as $a+b$ are circuits of $\Gamma$ whose wires the conclusion reads):
--   $$\mathrm{FFTConv}_{\mathrm{round}}(a+b,c)=\mathrm{FFTConv}_{\mathrm{round}}(a,c)+\mathrm{FFTConv}_{\mathrm{round}}(b,c)\quad(137a)$$
--   $$\mathrm{FFTConv}_{\mathrm{round}}(a,b)=\mathrm{FFTConv}_{\mathrm{round}}(b,a)\quad(137b),\qquad \mathrm{FFTConv}_{\mathrm{round}}(2a,b)=2\,\mathrm{FFTConv}_{\mathrm{round}}(a,b)\quad(137c)$$
--   $$\mathrm{FFTConv}_{\mathrm{round}}(-a,b)=-\mathrm{FFTConv}_{\mathrm{round}}(a,b)\quad(137d),\qquad \mathrm{FFTConv}_{\mathrm{round}}(\mathrm{CShift}_1a,b)=\mathrm{CShift}_1\mathrm{FFTConv}_{\mathrm{round}}(a,b)\quad(137e)$$
--   $$\mathrm{FFTConv}_{\mathrm{round}}(\mathrm{FFTConv}_{\mathrm{round}}(a,b),c)=\mathrm{FFTConv}_{\mathrm{round}}(a,\mathrm{FFTConv}_{\mathrm{round}}(b,c))\quad(137f).$$
--   Sums, differences and negations act on scale-zero words; doubling is a left shift; equality is the array check. These are the ring identities of the rounded convolution from which distributivity, associativity and commutativity of FFTMul follow.
--
--   Differences from the source:
--   - reading: a sound and implicationally complete finite set of rules, formulas over arbitrary unary or binary Boolean operators (p. 4) → the printed AX1–AX3 and modus ponens in circuit form (letters = wires, connectives = gates of the context) plus the axiom ⊤ for a constant-true gate; gate basis {⊤, ¬, →}, with ∧, ∨, ↔, ⊕ fixed 2–6-gate sub-circuits; reason: the paper fixes one such set and notes that the choice of operators and axiom schemes does not affect asymptotic size (footnote 1, p. 4)
--   - encoding: contexts of inputs, gate definitions and assertions; expanded context Γ ∪ Φ; circuits and premises supplied in Γ → Ctx = indexed wire list + assertion list; conclusion circuits appended by Build.expand; Contains maps a generated circuit into existing gates, fixing its input wires and preserving operators and edges; Asserts requires a contained check with asserted output; reason: structural wire mapping allows arbitrary surrounding circuitry, interleaving and shared gates, as required by Section 2.2; no contiguity assumption is imposed
--   - reading: O(f) cost of a family of big-step rules (p. 8) → one existential constant chosen before every universally quantified parameter, context and wire; reason: the paper: a family with cost O(f) has one constant for the whole family and every Γ meeting the requirements
--   - reading: W = O(L^4) a common bound on widths and scales (p. 53); O(W)-bit words; costs N log^{O(1)} N, N W^{O(1)}, W^{O(1)} → W := (L+1)^4; 'O(W)-bit' is ∀ cw, width ≤ cw·W (cw fixed before C, k); costs C·N·L^k, C·N·W^k, C·W^k with L = log₂ N; reason: the paper fixes W only up to a constant; any Θ(L^4) choice gives the same statement; L = log₂ N exactly since N = 2^L
--   - encoding: N, L of the multiplier fixed by n (p. 48), lemma stated for the multiplier's N → N, L of paperParams n, for every n ≥ 1; reason: the lemmas of Appendices G–I are used at exactly these parameters
-- source:
--   Krapivin, Li, Shi, Fine-Grained Proof Complexity for Elementary Arithmetic in Extended Frege, STOC 2027 submission (manuscript sha256 704dfb8a…), pp. 126-127, Lemma H.1 (137a)-(137f)

import Mathlib
import Definitions.Def_FineGrainedEF_Main_EF
import Definitions.Def_FineGrainedEF_Main_BoolCircuits
import Definitions.Def_FineGrainedEF_Main_IntCircuits
import Definitions.Def_FineGrainedEF_Main_ScaledArith
import Definitions.Def_FineGrainedEF_Main_FFTMul
import Definitions.Def_FineGrainedEF_Main_Checks

namespace FineGrainedEF.Main

/-- Lemma H.1 (Exact identities for rounded coefficient circuits), pp. 126–127. For every width
constant `cw` there are `C, k` such that, for every `n ≥ 1`, every well-formed `Γ` and all
length-`N` arrays `a, b, c` of signed scale-zero words of `Γ` of width at most `cw·W`, each of
(137a)–(137f) is derived at cost `C·N·L^k` from the bounds `‖h‖_∞ ≤ M` (`M = N^8`) on exactly the
arrays `h` fed to a rounded convolution in that conclusion; an array computed from `a, b, c`
(`a + b`, `2a`, `-a`, an inner rounded convolution) sits in `Γ`, and the conclusion reads its wires.
(137a) `FFTConv_round(a + b, c) = FFTConv_round(a, c) + FFTConv_round(b, c)`;
(137b) `FFTConv_round(a, b) = FFTConv_round(b, a)`;
(137c) `FFTConv_round(2a, b) = 2 FFTConv_round(a, b)`;
(137d) `FFTConv_round(-a, b) = -FFTConv_round(a, b)`;
(137e) `FFTConv_round(CShift_1 a, b) = CShift_1 FFTConv_round(a, b)`;
(137f) `FFTConv_round(FFTConv_round(a, b), c) = FFTConv_round(a, FFTConv_round(b, c))`. -/
theorem lemma_H_1 :
    ∀ cw : ℕ, ∃ C k : ℕ, ∀ (n : ℕ) (Γ : Ctx) (a b c : List (List ℕ)),
      1 ≤ n → Γ.WF →
      IsWordArray Γ a (paperParams n).N (cw * Wbound n) →
      IsWordArray Γ b (paperParams n).N (cw * Wbound n) →
      IsWordArray Γ c (paperParams n).N (cw * Wbound n) →
      -- (137a)
      (∀ s : List (List ℕ), Contains Γ (arrAdd a b) s →
        Asserts Γ (normLeM (paperParams n) s) → Asserts Γ (normLeM (paperParams n) c) →
        Asserts Γ (normLeM (paperParams n) a) → Asserts Γ (normLeM (paperParams n) b) →
        BigStep Γ
          (do let l ← fftConvRoundInt (paperParams n) s c
              let r₁ ← fftConvRoundInt (paperParams n) a c
              let r₂ ← fftConvRoundInt (paperParams n) b c
              let r ← arrAdd r₁ r₂
              let e ← arrEq l r
              pure [e])
          (C * (paperParams n).N * (paperParams n).L ^ k)) ∧
      -- (137b)
      (Asserts Γ (normLeM (paperParams n) a) → Asserts Γ (normLeM (paperParams n) b) →
        BigStep Γ
          (do let l ← fftConvRoundInt (paperParams n) a b
              let r ← fftConvRoundInt (paperParams n) b a
              let e ← arrEq l r
              pure [e])
          (C * (paperParams n).N * (paperParams n).L ^ k)) ∧
      -- (137c)
      (∀ d : List (List ℕ), Contains Γ (arrDouble a) d →
        Asserts Γ (normLeM (paperParams n) d) → Asserts Γ (normLeM (paperParams n) b) →
        Asserts Γ (normLeM (paperParams n) a) →
        BigStep Γ
          (do let l ← fftConvRoundInt (paperParams n) d b
              let r₀ ← fftConvRoundInt (paperParams n) a b
              let r ← arrDouble r₀
              let e ← arrEq l r
              pure [e])
          (C * (paperParams n).N * (paperParams n).L ^ k)) ∧
      -- (137d)
      (∀ d : List (List ℕ), Contains Γ (arrNeg a) d →
        Asserts Γ (normLeM (paperParams n) d) → Asserts Γ (normLeM (paperParams n) b) →
        Asserts Γ (normLeM (paperParams n) a) →
        BigStep Γ
          (do let l ← fftConvRoundInt (paperParams n) d b
              let r₀ ← fftConvRoundInt (paperParams n) a b
              let r ← arrNeg r₀
              let e ← arrEq l r
              pure [e])
          (C * (paperParams n).N * (paperParams n).L ^ k)) ∧
      -- (137e)
      (Asserts Γ (normLeM (paperParams n) (arrCShift1 a)) → Asserts Γ (normLeM (paperParams n) b) →
        Asserts Γ (normLeM (paperParams n) a) →
        BigStep Γ
          (do let l ← fftConvRoundInt (paperParams n) (arrCShift1 a) b
              let r₀ ← fftConvRoundInt (paperParams n) a b
              let e ← arrEq l (arrCShift1 r₀)
              pure [e])
          (C * (paperParams n).N * (paperParams n).L ^ k)) ∧
      -- (137f)
      (∀ ab bc : List (List ℕ), Contains Γ (fftConvRoundInt (paperParams n) a b) ab →
        Contains Γ (fftConvRoundInt (paperParams n) b c) bc →
        Asserts Γ (normLeM (paperParams n) a) → Asserts Γ (normLeM (paperParams n) b) →
        Asserts Γ (normLeM (paperParams n) c) → Asserts Γ (normLeM (paperParams n) ab) →
        Asserts Γ (normLeM (paperParams n) bc) →
        BigStep Γ
          (do let l ← fftConvRoundInt (paperParams n) ab c
              let r ← fftConvRoundInt (paperParams n) a bc
              let e ← arrEq l r
              pure [e])
          (C * (paperParams n).N * (paperParams n).L ^ k)) := by sorry

end FineGrainedEF.Main
