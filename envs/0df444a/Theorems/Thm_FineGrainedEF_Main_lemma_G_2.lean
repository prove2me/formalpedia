-- Prove2me | Theorems.Thm_FineGrainedEF_Main_lemma_G_2
-- name    : FineGrainedEF.Main.lemma_G_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:13:43.822782+00:00
-- url     : https://prove2.me/theorems/b1e33ff2-296f-4e5f-8016-c4e9a26bf505
-- title:
--   Lemma G.2 — coefficient bounds 0 ≤ FFTConv_round(a,b)_j ≤ NAB, ‖·‖∞ ≤ NAB, and zero entries from index r+s−1, each at cost N log^{O(1)} N
-- statement:
--   Fix a width constant $c_w$. For $n\ge1$ let $N=2^L$ and $L$ be the multiplier's parameters and $W=(L+1)^4$. Let $\Gamma$ be well formed, $a,b$ length-$N$ arrays of signed scale-zero words of $\Gamma$ of width at most $c_wW$, and $A,B$ nonnegative (unsigned) bound words of width at most $c_wW$, with the input bounds of Lemma G.1, $\|a\|_\infty\le M$ and $\|b\|_\infty\le M$ ($M=N^8$), asserted in $\Gamma$. There are $C,k$ (depending only on $c_w$) such that each of the following holds with cost $C\,N\,L^k$:
--   $$\Gamma:0\le a_j\le A,\ 0\le b_j\le B\ (j<N)\ \triangleright\ [0\le\mathrm{FFTConv}_{\mathrm{round}}(a,b)_j\le NAB]_{j<N}\quad(134),$$
--   $$\Gamma:\|a\|_\infty\le A,\ \|b\|_\infty\le B\ \triangleright\ \|\mathrm{FFTConv}_{\mathrm{round}}(a,b)\|_\infty\le NAB\quad(135),$$
--   and for $r,s\ge1$ with $r+s-1<N$,
--   $$\Gamma:[a_j=0]_{r\le j<N},\ [b_j=0]_{s\le j<N}\ \triangleright\ [\mathrm{FFTConv}_{\mathrm{round}}(a,b)_j=0]_{r+s-1\le j<N}\quad(136).$$
--   These bounds supply the ranges and the vanishing high coefficients that carry resolution needs.
--
--   Differences from the source:
--   - reading: a sound and implicationally complete finite set of rules, formulas over arbitrary unary or binary Boolean operators (p. 4) → the printed AX1–AX3 and modus ponens in circuit form (letters = wires, connectives = gates of the context) plus the axiom ⊤ for a constant-true gate; gate basis {⊤, ¬, →}, with ∧, ∨, ↔, ⊕ fixed 2–6-gate sub-circuits; reason: the paper fixes one such set and notes that the choice of operators and axiom schemes does not affect asymptotic size (footnote 1, p. 4)
--   - encoding: contexts of inputs, gate definitions and assertions; expanded context Γ ∪ Φ; circuits and premises supplied in Γ → Ctx = indexed wire list + assertion list; conclusion circuits appended by Build.expand; Contains maps a generated circuit into existing gates, fixing its input wires and preserving operators and edges; Asserts requires a contained check with asserted output; reason: structural wire mapping allows arbitrary surrounding circuitry, interleaving and shared gates, as required by Section 2.2; no contiguity assumption is imposed
--   - reading: O(f) cost of a family of big-step rules (p. 8) → one existential constant chosen before every universally quantified parameter, context and wire; reason: the paper: a family with cost O(f) has one constant for the whole family and every Γ meeting the requirements
--   - reading: W = O(L^4) a common bound on widths and scales (p. 53); O(W)-bit words; costs N log^{O(1)} N, N W^{O(1)}, W^{O(1)} → W := (L+1)^4; 'O(W)-bit' is ∀ cw, width ≤ cw·W (cw fixed before C, k); costs C·N·L^k, C·N·W^k, C·W^k with L = log₂ N; reason: the paper fixes W only up to a constant; any Θ(L^4) choice gives the same statement; L = log₂ N exactly since N = 2^L
--   - encoding: N, L of the multiplier fixed by n (p. 48), lemma stated for the multiplier's N → N, L of paperParams n, for every n ≥ 1; reason: the lemmas of Appendices G–I are used at exactly these parameters
--   - reading: nonnegative bound words A, B; the word NAB; the check 0 ≤ x ≤ A → A, B unsigned words; NAB := MulInt(2^L·A, B) with A, B zero-extended to signed words; 0 ≤ x ≤ A := (0 ≤ x) ∧ (x ≤ A); reason: the paper leaves the encoding of the bound words and the bracketing of NAB open; all choices give the same values
-- source:
--   Krapivin, Li, Shi, Fine-Grained Proof Complexity for Elementary Arithmetic in Extended Frege, STOC 2027 submission (manuscript sha256 704dfb8a…), pp. 125-126, Lemma G.2 (134)-(136)

import Mathlib
import Definitions.Def_FineGrainedEF_Main_EF
import Definitions.Def_FineGrainedEF_Main_BoolCircuits
import Definitions.Def_FineGrainedEF_Main_IntCircuits
import Definitions.Def_FineGrainedEF_Main_ScaledArith
import Definitions.Def_FineGrainedEF_Main_FFTMul
import Definitions.Def_FineGrainedEF_Main_Checks

namespace FineGrainedEF.Main

/-- Lemma G.2 (Coefficient bounds and zero entries), pp. 125–126. For every width constant `cw`
(the `O(W)` of the hypotheses) there are `C, k` such that, for every `n ≥ 1` (parameters
`N = 2^L`, `L`, `W = (L+1)^4` of `paperParams n`), every well-formed `Γ`, all length-`N` arrays
`a, b` of signed scale-zero words of `Γ` of width at most `cw·W`, and all nonnegative (unsigned)
bound words `A, B` of `Γ` of width at most `cw·W`, with the input bounds of Lemma G.1,
`‖a‖_∞ ≤ M`, `‖b‖_∞ ≤ M`, asserted in `Γ`, each of (134), (135), (136) holds with cost
`C·N·L^k` (`N log^{O(1)} N`):
(134) `Γ : [0 ≤ a_j ≤ A], [0 ≤ b_j ≤ B] (j < N) ▷ [0 ≤ FFTConv_round(a, b)_j ≤ NAB]_{j<N}`;
(135) `Γ : ‖a‖_∞ ≤ A, ‖b‖_∞ ≤ B ▷ ‖FFTConv_round(a, b)‖_∞ ≤ NAB`;
(136) for `r, s ≥ 1` with `r + s - 1 < N`:
`Γ : [a_j = 0]_{r≤j<N}, [b_j = 0]_{s≤j<N} ▷ [FFTConv_round(a, b)_j = 0]_{r+s-1≤j<N}`. -/
theorem lemma_G_2 :
    ∀ cw : ℕ, ∃ C k : ℕ, ∀ (n : ℕ) (Γ : Ctx) (a b : List (List ℕ)) (A B : List ℕ),
      1 ≤ n → Γ.WF →
      IsWordArray Γ a (paperParams n).N (cw * Wbound n) →
      IsWordArray Γ b (paperParams n).N (cw * Wbound n) →
      Γ.HasWires (A ++ B) → 1 ≤ A.length → A.length ≤ cw * Wbound n →
      1 ≤ B.length → B.length ≤ cw * Wbound n →
      Asserts Γ (normLeM (paperParams n) a) → Asserts Γ (normLeM (paperParams n) b) →
      -- (134)
      ((∀ j < (paperParams n).N, Asserts Γ (rangeChk (a.getD j []) A false)) →
        (∀ j < (paperParams n).N, Asserts Γ (rangeChk (b.getD j []) B false)) →
        BigStep Γ
          (do let c ← fftConvRoundInt (paperParams n) a b
              let e ← nab (paperParams n) A B
              c.mapM fun x => rangeChk x e true)
          (C * (paperParams n).N * (paperParams n).L ^ k)) ∧
      -- (135)
      (Asserts Γ (normLe a true A) → Asserts Γ (normLe b true B) →
        BigStep Γ
          (do let c ← fftConvRoundInt (paperParams n) a b
              let e ← nab (paperParams n) A B
              let d ← normLe c true e
              pure [d])
          (C * (paperParams n).N * (paperParams n).L ^ k)) ∧
      -- (136)
      (∀ r s : ℕ, 1 ≤ r → 1 ≤ s → r + s - 1 < (paperParams n).N →
        (∀ j, r ≤ j → j < (paperParams n).N → Asserts Γ (isZero (a.getD j []) true)) →
        (∀ j, s ≤ j → j < (paperParams n).N → Asserts Γ (isZero (b.getD j []) true)) →
        BigStep Γ
          (do let c ← fftConvRoundInt (paperParams n) a b
              ((List.range (paperParams n).N).filter fun j => r + s - 1 ≤ j).mapM fun j =>
                isZero (c.getD j []) true)
          (C * (paperParams n).N * (paperParams n).L ^ k)) := by sorry

end FineGrainedEF.Main
