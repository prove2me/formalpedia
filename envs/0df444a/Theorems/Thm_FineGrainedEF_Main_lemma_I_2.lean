-- Prove2me | Theorems.Thm_FineGrainedEF_Main_lemma_I_2
-- name    : FineGrainedEF.Main.lemma_I_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:13:45.055542+00:00
-- url     : https://prove2.me/theorems/b4d894e4-2a39-4156-82e6-11bee73949c1
-- title:
--   Lemma I.2 — carry resolution may be deferred across a rounded convolution, in either argument
-- statement:
--   Fix a width constant $c_w$. For $n\ge1$ let $N,L$ be the multiplier's parameters, $W=(L+1)^4$, $M=N^8$. Let $\Gamma$ be well formed, $a,z$ length-$N$ arrays of signed scale-zero words of $\Gamma$ of width at most $c_wW$, and let $\Gamma$ contain $b:=\mathrm{Carry}(a)$ with carries $\kappa_0,\dots,\kappa_N$; put $u:=(\kappa_1,\dots,\kappa_N)$. Let $R$ assert: $a\ge0$ entrywise, $\kappa_N=0$, $\|h\|_\infty\le M$ for each $h\in\{a,b,z,u,2u,\mathrm{Shift}\,u,a-b\}$, and $\mathrm{FFTConv}_{\mathrm{round}}(u,z)_{N-1}=0$. There are $C,k$ (depending only on $c_w$) such that
--   $$\Gamma:R\ \triangleright^{CNL^k}\ \mathrm{Carry}(\mathrm{FFTConv}_{\mathrm{round}}(a,z))=\mathrm{Carry}(\mathrm{FFTConv}_{\mathrm{round}}(b,z))\ (146a),\quad \mathrm{Carry}(\mathrm{FFTConv}_{\mathrm{round}}(z,a))=\mathrm{Carry}(\mathrm{FFTConv}_{\mathrm{round}}(z,b))\ (146b).$$
--   The bit array $b$ enters as two-bit scale-zero coefficients. This lets the multiplier resolve carries of an inner product before an outer multiplication.
--
--   Differences from the source:
--   - reading: a sound and implicationally complete finite set of rules, formulas over arbitrary unary or binary Boolean operators (p. 4) → the printed AX1–AX3 and modus ponens in circuit form (letters = wires, connectives = gates of the context) plus the axiom ⊤ for a constant-true gate; gate basis {⊤, ¬, →}, with ∧, ∨, ↔, ⊕ fixed 2–6-gate sub-circuits; reason: the paper fixes one such set and notes that the choice of operators and axiom schemes does not affect asymptotic size (footnote 1, p. 4)
--   - encoding: contexts of inputs, gate definitions and assertions; expanded context Γ ∪ Φ; circuits and premises supplied in Γ → Ctx = indexed wire list + assertion list; conclusion circuits appended by Build.expand; Contains maps a generated circuit into existing gates, fixing its input wires and preserving operators and edges; Asserts requires a contained check with asserted output; reason: structural wire mapping allows arbitrary surrounding circuitry, interleaving and shared gates, as required by Section 2.2; no contiguity assumption is imposed
--   - reading: O(f) cost of a family of big-step rules (p. 8) → one existential constant chosen before every universally quantified parameter, context and wire; reason: the paper: a family with cost O(f) has one constant for the whole family and every Γ meeting the requirements
--   - reading: W = O(L^4) a common bound on widths and scales (p. 53); O(W)-bit words; costs N log^{O(1)} N, N W^{O(1)}, W^{O(1)} → W := (L+1)^4; 'O(W)-bit' is ∀ cw, width ≤ cw·W (cw fixed before C, k); costs C·N·L^k, C·N·W^k, C·W^k with L = log₂ N; reason: the paper fixes W only up to a constant; any Θ(L^4) choice gives the same statement; L = log₂ N exactly since N = 2^L
--   - encoding: N, L of the multiplier fixed by n (p. 48), lemma stated for the multiplier's N → N, L of paperParams n, for every n ≥ 1; reason: the lemmas of Appendices G–I are used at exactly these parameters
-- source:
--   Krapivin, Li, Shi, Fine-Grained Proof Complexity for Elementary Arithmetic in Extended Frege, STOC 2027 submission (manuscript sha256 704dfb8a…), p. 131, Lemma I.2 (146a)-(146b)

import Mathlib
import Definitions.Def_FineGrainedEF_Main_EF
import Definitions.Def_FineGrainedEF_Main_BoolCircuits
import Definitions.Def_FineGrainedEF_Main_IntCircuits
import Definitions.Def_FineGrainedEF_Main_ScaledArith
import Definitions.Def_FineGrainedEF_Main_FFTMul
import Definitions.Def_FineGrainedEF_Main_Checks

namespace FineGrainedEF.Main

/-- Lemma I.2 (Carry resolution may be deferred across multiplication), p. 131. For every width
constant `cw` there are `C, k` such that, for every `n ≥ 1`, every well-formed `Γ` and all
length-`N` arrays `a, z` of signed scale-zero words of `Γ` of width at most `cw·W`, with
`b := Carry(a)` and its carries `κ_0, …, κ_N` in `Γ` and `u := (κ_1, …, κ_N)`, from `R`:
`a ≥ 0` entrywise, `κ_N = 0`, `‖h‖_∞ ≤ M` for `h ∈ {a, b, z, u, 2u, Shift u, a - b}`, and
`FFTConv_round(u, z)_{N-1} = 0`, with cost `C·N·L^k`:
(146a) `Carry(FFTConv_round(a, z)) = Carry(FFTConv_round(b, z))` and
(146b) `Carry(FFTConv_round(z, a)) = Carry(FFTConv_round(z, b))`
(the bit array `b` as scale-zero two-bit coefficients). -/
theorem lemma_I_2 :
    ∀ cw : ℕ, ∃ C k : ℕ, ∀ (n : ℕ) (Γ : Ctx) (a z : List (List ℕ)) (b : List ℕ)
      (κ : List (List ℕ)),
      1 ≤ n → Γ.WF →
      IsWordArray Γ a (paperParams n).N (cw * Wbound n) →
      IsWordArray Γ z (paperParams n).N (cw * Wbound n) →
      Contains Γ (carry a) (b, κ) →
      (∀ j < (paperParams n).N, Asserts Γ (nonneg (a.getD j []))) →
      Asserts Γ (isZero (κ.getD (paperParams n).N []) true) →
      Asserts Γ (normLeM (paperParams n) a) →
      Asserts Γ (do let bD ← bitsD0 b; normLeM (paperParams n) bD) →
      Asserts Γ (normLeM (paperParams n) z) →
      Asserts Γ (normLeM (paperParams n) (κ.drop 1)) →
      Asserts Γ (do let d ← arrDouble (κ.drop 1); normLeM (paperParams n) d) →
      Asserts Γ (do let sh ← arrShift (κ.drop 1); normLeM (paperParams n) sh) →
      Asserts Γ (do let bD ← bitsD0 b; let d ← arrSub a bD; normLeM (paperParams n) d) →
      Asserts Γ (do let c ← fftConvRoundInt (paperParams n) (κ.drop 1) z
                    isZero (c.getD ((paperParams n).N - 1) []) true) →
      BigStep Γ
        (do let bD ← bitsD0 b
            let ca ← fftConvRoundInt (paperParams n) a z
            let cb ← fftConvRoundInt (paperParams n) bD z
            let r₁ ← carry ca
            let r₂ ← carry cb
            let e₁ ← eqBits r₁.1 r₂.1
            let ca' ← fftConvRoundInt (paperParams n) z a
            let cb' ← fftConvRoundInt (paperParams n) z bD
            let s₁ ← carry ca'
            let s₂ ← carry cb'
            let e₂ ← eqBits s₁.1 s₂.1
            pure [e₁, e₂])
        (C * (paperParams n).N * (paperParams n).L ^ k) := by sorry

end FineGrainedEF.Main
