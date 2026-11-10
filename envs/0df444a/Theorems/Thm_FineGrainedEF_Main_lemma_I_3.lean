-- Prove2me | Theorems.Thm_FineGrainedEF_Main_lemma_I_3
-- name    : FineGrainedEF.Main.lemma_I_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:13:33.090368+00:00
-- url     : https://prove2.me/theorems/f4b5c712-183d-4847-8e96-b82e04b97a90
-- title:
--   Lemma I.3 — carry bounds 0 ≤ κ_j ≤ A and termination: carries and output bits vanish from index r + ⌈log(A+1)⌉
-- statement:
--   Fix a width constant $c_w$. For $n\ge1$ let $N,L$ be the multiplier's parameters and $W=(L+1)^4$. Let $\Gamma$ be well formed and contain $b:=\mathrm{Carry}(a)$ for a length-$N$ array $a$ of signed words of width at most $c_wW$, with carries $\kappa_0=0$, $\kappa_{j+1}=\lfloor(a_j+\kappa_j)/2\rfloor$. Let $A$ be a nonnegative integer whose literal has width at most $c_wW$. There are $C,k$ (depending only on $c_w$) such that
--   $$\Gamma:[0\le a_j\le A]_{j<N}\ \triangleright^{C N W^k}\ [0\le\kappa_j\le A]_{j\le N}\quad(148),$$
--   and, with $q:=\lceil\log_2(A+1)\rceil$, for every $r\ge0$ with $r+q\le N$,
--   $$\Gamma:[0\le a_j\le A]_{j<N},\ [a_j=0]_{r\le j<N}\ \triangleright^{C N W^k}\ [\kappa_j=0]_{r+q\le j\le N},\ [b_j=0]_{r+q\le j<N}\quad(149).$$
--   Carry resolution therefore terminates: the output bits and carries vanish beyond the support of the input plus $q$ positions.
--
--   Differences from the source:
--   - reading: a sound and implicationally complete finite set of rules, formulas over arbitrary unary or binary Boolean operators (p. 4) → the printed AX1–AX3 and modus ponens in circuit form (letters = wires, connectives = gates of the context) plus the axiom ⊤ for a constant-true gate; gate basis {⊤, ¬, →}, with ∧, ∨, ↔, ⊕ fixed 2–6-gate sub-circuits; reason: the paper fixes one such set and notes that the choice of operators and axiom schemes does not affect asymptotic size (footnote 1, p. 4)
--   - encoding: contexts of inputs, gate definitions and assertions; expanded context Γ ∪ Φ; circuits and premises supplied in Γ → Ctx = indexed wire list + assertion list; conclusion circuits appended by Build.expand; Contains maps a generated circuit into existing gates, fixing its input wires and preserving operators and edges; Asserts requires a contained check with asserted output; reason: structural wire mapping allows arbitrary surrounding circuitry, interleaving and shared gates, as required by Section 2.2; no contiguity assumption is imposed
--   - reading: O(f) cost of a family of big-step rules (p. 8) → one existential constant chosen before every universally quantified parameter, context and wire; reason: the paper: a family with cost O(f) has one constant for the whole family and every Γ meeting the requirements
--   - reading: W = O(L^4) a common bound on widths and scales (p. 53); O(W)-bit words; costs N log^{O(1)} N, N W^{O(1)}, W^{O(1)} → W := (L+1)^4; 'O(W)-bit' is ∀ cw, width ≤ cw·W (cw fixed before C, k); costs C·N·L^k, C·N·W^k, C·W^k with L = log₂ N; reason: the paper fixes W only up to a constant; any Θ(L^4) choice gives the same statement; L = log₂ N exactly since N = 2^L
--   - encoding: N, L of the multiplier fixed by n (p. 48), lemma stated for the multiplier's N → N, L of paperParams n, for every n ≥ 1; reason: the lemmas of Appendices G–I are used at exactly these parameters
--   - encoding: a fixed nonnegative integer A of width O(W); checks 0 ≤ x ≤ A, b_j = 0 → A : ℕ with litWidth A ≤ cw·W, hardwired as an integer literal; 0 ≤ x ≤ A := (0 ≤ x) ∧ (x ≤ A); b_j = 0 compares the one-bit unsigned word with the literal 0; reason: A is a fixed number, hence a hardwired literal; the checks are those of C.1
-- source:
--   Krapivin, Li, Shi, Fine-Grained Proof Complexity for Elementary Arithmetic in Extended Frege, STOC 2027 submission (manuscript sha256 704dfb8a…), p. 132, Lemma I.3 (148)-(149)

import Mathlib
import Definitions.Def_FineGrainedEF_Main_EF
import Definitions.Def_FineGrainedEF_Main_BoolCircuits
import Definitions.Def_FineGrainedEF_Main_IntCircuits
import Definitions.Def_FineGrainedEF_Main_ScaledArith
import Definitions.Def_FineGrainedEF_Main_FFTMul
import Definitions.Def_FineGrainedEF_Main_Checks

namespace FineGrainedEF.Main

/-- Lemma I.3 (Bounds and termination of carry resolution), p. 132. For every width constant `cw`
there are `C, k` such that, for every `n ≥ 1`, every well-formed `Γ` containing the carry
resolution `b := Carry(a)` of a length-`N` array `a` of signed words of width at most `cw·W`
(output bits `b_j`, carries `κ_0, …, κ_N`), and every nonnegative integer `A` whose literal has
width at most `cw·W`, with cost `C·N·W^k` (`N W^{O(1)}`):
(148) `Γ : [0 ≤ a_j ≤ A]_{j<N} ▷ [0 ≤ κ_j ≤ A]_{j≤N}`;
(149) with `q := ⌈log₂(A+1)⌉`, for every `r ≥ 0` with `r + q ≤ N`:
`Γ : [0 ≤ a_j ≤ A]_{j<N}, [a_j = 0]_{r≤j<N} ▷ [κ_j = 0]_{r+q≤j≤N}, [b_j = 0]_{r+q≤j<N}`. -/
theorem lemma_I_3 :
    ∀ cw : ℕ, ∃ C k : ℕ, ∀ (n : ℕ) (Γ : Ctx) (a : List (List ℕ)) (A : ℕ) (b : List ℕ)
      (κ : List (List ℕ)),
      1 ≤ n → Γ.WF →
      IsWordArray Γ a (paperParams n).N (cw * Wbound n) →
      litWidth A ≤ cw * Wbound n →
      Contains Γ (carry a) (b, κ) →
      (∀ j < (paperParams n).N, Asserts Γ (do let e ← intLit A; rangeChk (a.getD j []) e true)) →
      -- (148)
      BigStep Γ
          ((List.range ((paperParams n).N + 1)).mapM fun j => do
            let e ← intLit A
            rangeChk (κ.getD j []) e true)
          (C * (paperParams n).N * Wbound n ^ k) ∧
      -- (149)
      (∀ r : ℕ, r + Nat.clog 2 (A + 1) ≤ (paperParams n).N →
        (∀ j, r ≤ j → j < (paperParams n).N → Asserts Γ (isZero (a.getD j []) true)) →
        BigStep Γ
          (do let ks ← ((List.range ((paperParams n).N + 1)).filter
                  fun j => r + Nat.clog 2 (A + 1) ≤ j).mapM fun j => isZero (κ.getD j []) true
              let bs ← ((List.range (paperParams n).N).filter
                  fun j => r + Nat.clog 2 (A + 1) ≤ j).mapM fun j => isZero [b.getD j 0] false
              pure (ks ++ bs))
          (C * (paperParams n).N * Wbound n ^ k)) := by sorry

end FineGrainedEF.Main
