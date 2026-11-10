-- Prove2me | Theorems.Thm_FineGrainedEF_Main_lemma_I_1
-- name    : FineGrainedEF.Main.lemma_I_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:13:41.534733+00:00
-- url     : https://prove2.me/theorems/71eb40bf-430f-44e3-899a-2a8e5b31d381
-- title:
--   Lemma I.1 — carry identities: carry certificates, Carry(a + a′) = ADD(Carry(a), Carry(a′)), a − Carry(a) = 2u − Shift u
-- statement:
--   Fix a width constant $c_w$. For $n\ge1$ let $N,L$ be the multiplier's parameters and $W=(L+1)^4$. Let $\Gamma$ be well formed and $a,a',u$ length-$N$ arrays of signed words of $\Gamma$ of width at most $c_wW$. There are $C,k$ (depending only on $c_w$) such that
--   $$\Gamma:u_{N-1}=0\ \triangleright^{CNL^k}\ \mathrm{Carry}(a+2u-\mathrm{Shift}\,u)=\mathrm{Carry}(a)\quad(141);$$
--   with $\mathrm{Carry}(a)$, $\mathrm{Carry}(a')$, $a+a'$, $\mathrm{Carry}(a+a')$ and $\mathrm{ADD}(\mathrm{Carry}(a),\mathrm{Carry}(a'))$ in $\Gamma$ and $R$ asserting that $a,a'$ are nonnegative entrywise, the terminal carries of $a$, $a'$, $a+a'$ vanish and the final carry of the output adder vanishes,
--   $$\Gamma:R\ \triangleright^{CNL^k}\ \mathrm{Carry}(a+a')=\mathrm{ADD}(\mathrm{Carry}(a),\mathrm{Carry}(a'))\quad(142);$$
--   and with $b:=\mathrm{Carry}(a)$ in $\Gamma$, carries $\kappa_j$, $u_j:=\kappa_{j+1}$,
--   $$\Gamma\ \triangleright^{CNL^k}\ a-b=2u-\mathrm{Shift}\,u\quad(143),\qquad \Gamma:\kappa_N=0\ \triangleright^{CW^k}\ u_{N-1}=0\quad(144).$$
--   These identities let carry resolution be compared across different coefficient arrays representing the same integer.
--
--   Differences from the source:
--   - reading: a sound and implicationally complete finite set of rules, formulas over arbitrary unary or binary Boolean operators (p. 4) → the printed AX1–AX3 and modus ponens in circuit form (letters = wires, connectives = gates of the context) plus the axiom ⊤ for a constant-true gate; gate basis {⊤, ¬, →}, with ∧, ∨, ↔, ⊕ fixed 2–6-gate sub-circuits; reason: the paper fixes one such set and notes that the choice of operators and axiom schemes does not affect asymptotic size (footnote 1, p. 4)
--   - encoding: contexts of inputs, gate definitions and assertions; expanded context Γ ∪ Φ; circuits and premises supplied in Γ → Ctx = indexed wire list + assertion list; conclusion circuits appended by Build.expand; Contains maps a generated circuit into existing gates, fixing its input wires and preserving operators and edges; Asserts requires a contained check with asserted output; reason: structural wire mapping allows arbitrary surrounding circuitry, interleaving and shared gates, as required by Section 2.2; no contiguity assumption is imposed
--   - reading: O(f) cost of a family of big-step rules (p. 8) → one existential constant chosen before every universally quantified parameter, context and wire; reason: the paper: a family with cost O(f) has one constant for the whole family and every Γ meeting the requirements
--   - reading: W = O(L^4) a common bound on widths and scales (p. 53); O(W)-bit words; costs N log^{O(1)} N, N W^{O(1)}, W^{O(1)} → W := (L+1)^4; 'O(W)-bit' is ∀ cw, width ≤ cw·W (cw fixed before C, k); costs C·N·L^k, C·N·W^k, C·W^k with L = log₂ N; reason: the paper fixes W only up to a constant; any Θ(L^4) choice gives the same statement; L = log₂ N exactly since N = 2^L
--   - encoding: N, L of the multiplier fixed by n (p. 48), lemma stated for the multiplier's N → N, L of paperParams n, for every n ≥ 1; reason: the lemmas of Appendices G–I are used at exactly these parameters
--   - encoding: R: a, a′ nonnegative; terminal carries vanish; final carry of the output adder vanishes → [0 ≤ a_j], [0 ≤ a′_j] for j < N; κ_N = 0 for the three carry circuits; the negation of the last output bit of ADD(Carry(a), Carry(a′)) asserted; reason: the assertions of R as C.1 checks; a vanishing bit is the assertion of its negation
-- source:
--   Krapivin, Li, Shi, Fine-Grained Proof Complexity for Elementary Arithmetic in Extended Frege, STOC 2027 submission (manuscript sha256 704dfb8a…), p. 130, Lemma I.1 (141)-(144)

import Mathlib
import Definitions.Def_FineGrainedEF_Main_EF
import Definitions.Def_FineGrainedEF_Main_BoolCircuits
import Definitions.Def_FineGrainedEF_Main_IntCircuits
import Definitions.Def_FineGrainedEF_Main_ScaledArith
import Definitions.Def_FineGrainedEF_Main_FFTMul
import Definitions.Def_FineGrainedEF_Main_Checks

namespace FineGrainedEF.Main

/-- Lemma I.1 (Carry identities from local gates), p. 130. For every width constant `cw` there are
`C, k` such that, for every `n ≥ 1`, every well-formed `Γ` and all length-`N` arrays `a, a', u` of
signed words of `Γ` of width at most `cw·W`:
(141) `Γ : u_{N-1} = 0 ▷^{N log^{O(1)} N} Carry(a + 2u - Shift u) = Carry(a)`;
(142) with `Carry(a)`, `Carry(a')`, `a + a'`, `Carry(a + a')` and the output adder
`ADD(Carry(a), Carry(a'))` in `Γ`, and `R`: `a, a'` nonnegative entrywise, the terminal carries of
`Carry(a)`, `Carry(a')`, `Carry(a + a')` zero, and the final carry (last bit) of the output adder
zero: `Γ : R ▷^{N log^{O(1)} N} Carry(a + a') = ADD(Carry(a), Carry(a'))`;
(143) with `b := Carry(a)` and its carries `κ_j` in `Γ`, `u_j := κ_{j+1}`:
`Γ ▷^{N log^{O(1)} N} a - b = 2u - Shift u`;
(144) `Γ : κ_N = 0 ▷^{W^{O(1)}} u_{N-1} = 0`. -/
theorem lemma_I_1 :
    ∀ cw : ℕ, ∃ C k : ℕ, ∀ (n : ℕ) (Γ : Ctx) (a a' u : List (List ℕ)),
      1 ≤ n → Γ.WF →
      IsWordArray Γ a (paperParams n).N (cw * Wbound n) →
      IsWordArray Γ a' (paperParams n).N (cw * Wbound n) →
      IsWordArray Γ u (paperParams n).N (cw * Wbound n) →
      -- (141)
      (Asserts Γ (isZero (u.getD ((paperParams n).N - 1) []) true) →
        BigStep Γ
          (do let d ← arrDouble u
              let t ← arrAdd a d
              let sh ← arrShift u
              let s ← arrSub t sh
              let c₁ ← carry s
              let c₂ ← carry a
              let e ← eqBits c₁.1 c₂.1
              pure [e])
          (C * (paperParams n).N * (paperParams n).L ^ k)) ∧
      -- (142)
      (∀ (ba ba' bs o : List ℕ) (κa κa' κs s : List (List ℕ)),
        Contains Γ (carry a) (ba, κa) → Contains Γ (carry a') (ba', κa') →
        Contains Γ (arrAdd a a') s → Contains Γ (carry s) (bs, κs) → Contains Γ (ADD ba ba') o →
        (∀ j < (paperParams n).N, Asserts Γ (nonneg (a.getD j [])) ∧ Asserts Γ (nonneg (a'.getD j []))) →
        Asserts Γ (isZero (κa.getD (paperParams n).N []) true) →
        Asserts Γ (isZero (κa'.getD (paperParams n).N []) true) →
        Asserts Γ (isZero (κs.getD (paperParams n).N []) true) →
        Asserts Γ (notG (o.getLastD 0)) →
        BigStep Γ (do let e ← eqBits bs o; pure [e])
          (C * (paperParams n).N * (paperParams n).L ^ k)) ∧
      -- (143)
      (∀ (b : List ℕ) (κ : List (List ℕ)), Contains Γ (carry a) (b, κ) →
        BigStep Γ
          (do let bD ← bitsD0 b
              let l ← arrSub a bD
              let d ← arrDouble (κ.drop 1)
              let sh ← arrShift (κ.drop 1)
              let r ← arrSub d sh
              let e ← arrEq l r
              pure [e])
          (C * (paperParams n).N * (paperParams n).L ^ k)) ∧
      -- (144)
      (∀ (b : List ℕ) (κ : List (List ℕ)), Contains Γ (carry a) (b, κ) →
        Asserts Γ (isZero (κ.getD (paperParams n).N []) true) →
        BigStep Γ
          (do let e ← isZero ((κ.drop 1).getD ((paperParams n).N - 1) []) true
              pure [e])
          (C * Wbound n ^ k)) := by sorry

end FineGrainedEF.Main
