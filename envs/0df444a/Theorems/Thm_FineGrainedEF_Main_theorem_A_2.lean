-- Prove2me | Theorems.Thm_FineGrainedEF_Main_theorem_A_2
-- name    : FineGrainedEF.Main.theorem_A_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:13:31.334126+00:00
-- url     : https://prove2.me/theorems/3c493e9f-bfe4-4abe-bdf5-ddbd46011054
-- title:
--   Theorem A.2 — quasi-linear-size EF proofs of distributivity, associativity and commutativity of FFTMul, and linear-size proofs of associativity and commutativity of ADD
-- statement:
--   Let $\mathrm{ADD}$ be the schoolbook ripple-carry adder and $\mathrm{FFTMul}$ the FFT multiplier of Appendix A, whose parameters $N,L,p,t$ and hardwired roots and twiddles are fixed by $n$ for the whole computation, nested products included.
--
--   **(i)** There are constants $C,k$ such that for every $n\ge1$, every well-formed context $\Gamma$ and all unsigned $n$-bit words $x,y,z$ of $\Gamma$: adding to $\Gamma$ the gate definitions of
--   $$\mathrm{FFTMul}(x,\mathrm{ADD}(y,z)),\ \mathrm{ADD}(\mathrm{FFTMul}(x,y),\mathrm{FFTMul}(x,z)),\ \mathrm{FFTMul}(\mathrm{FFTMul}(x,y),z),\ \mathrm{FFTMul}(x,\mathrm{FFTMul}(y,z)),\ \mathrm{FFTMul}(x,y),\ \mathrm{FFTMul}(y,x)$$
--   (identical sub-circuits shared) and the three output equality checks $\mathrm{EQ}$ (outputs zero-padded to a common length), there is an EF derivation asserting
--   $$\mathrm{FFTMul}(x,\mathrm{ADD}(y,z))=\mathrm{ADD}(\mathrm{FFTMul}(x,y),\mathrm{FFTMul}(x,z)),\quad \mathrm{FFTMul}(\mathrm{FFTMul}(x,y),z)=\mathrm{FFTMul}(x,\mathrm{FFTMul}(y,z)),\quad \mathrm{FFTMul}(x,y)=\mathrm{FFTMul}(y,x),$$
--   and (gates of these circuits and checks) + (EF steps of the derivation) $\le C\,n\,\lfloor\log_2(n+2)\rfloor^k$.
--
--   **(ii)** There is $C'$ such that for every $n\ge1$, $\Gamma$, $x,y,z$ as above, the same holds for
--   $$\mathrm{ADD}(\mathrm{ADD}(x,y),z)=\mathrm{ADD}(x,\mathrm{ADD}(y,z)),\qquad \mathrm{ADD}(x,y)=\mathrm{ADD}(y,x)$$
--   with total size at most $C'n$.
--
--   These are the laws of arithmetic for concrete binary circuits, proved in Extended Frege in size quasi-linear (multiplier) and linear (adder) in the circuit size — the first such fine-grained bounds; the natural coordinate-by-coordinate proof is quadratic.
--
--   Differences from the source:
--   - reading: a sound and implicationally complete finite set of rules, formulas over arbitrary unary or binary Boolean operators (p. 4) → the printed AX1–AX3 and modus ponens in circuit form (letters = wires, connectives = gates of the context) plus the axiom ⊤ for a constant-true gate; gate basis {⊤, ¬, →}, with ∧, ∨, ↔, ⊕ fixed 2–6-gate sub-circuits; reason: the paper fixes one such set and notes that the choice of operators and axiom schemes does not affect asymptotic size (footnote 1, p. 4)
--   - encoding: contexts of inputs, gate definitions and assertions; expanded context Γ ∪ Φ; circuits and premises supplied in Γ → Ctx = indexed wire list + assertion list; conclusion circuits appended by Build.expand; Contains maps a generated circuit into existing gates, fixing its input wires and preserving operators and edges; Asserts requires a contained check with asserted output; reason: structural wire mapping allows arbitrary surrounding circuitry, interleaving and shared gates, as required by Section 2.2; no contiguity assumption is imposed
--   - reading: O(f) cost of a family of big-step rules (p. 8) → one existential constant chosen before every universally quantified parameter, context and wire; reason: the paper: a family with cost O(f) has one constant for the whole family and every Γ meeting the requirements
--   - reading: Γ ▷^{n log^{O(1)}(n+2)} / ▷^{O(n)}, with 'the additional and complete proof bounds agree' (p. 54) → the complete size: gates of the conclusion circuits plus EF steps ≤ C·n·⌊log₂(n+2)⌋^k (resp. ≤ C′·n); reason: the paper states both bounds agree; the complete bound is the stronger of the two
--   - encoding: log(n+2) real logarithm → ⌊log₂(n+2)⌋; reason: ⌊log₂(n+2)⌋ ≥ 1 and is within a factor 2 of log₂(n+2) for n ≥ 1, so the O-classes coincide
--   - reading: x, y, z unsigned n-bit words available in Γ; identical sub-circuits FFTMul(x, y), ADD(y, z) of the joint computation → every well-formed Γ and wires x, y, z of Γ; FFTMul(x, y) built once and shared by the three identities, ADD(y, z) once; reason: Γ arbitrary per the convention of p. 8; Γ ∪ Φ is a union, so the same circuit occurring twice is one circuit
-- source:
--   Krapivin, Li, Shi, Fine-Grained Proof Complexity for Elementary Arithmetic in Extended Frege, STOC 2027 submission (manuscript sha256 704dfb8a…), p. 54, Theorem A.2 (proof: Appendix J, pp. 133-140); informal version Theorem 1.1, p. 3

import Mathlib
import Definitions.Def_FineGrainedEF_Main_EF
import Definitions.Def_FineGrainedEF_Main_BoolCircuits
import Definitions.Def_FineGrainedEF_Main_IntCircuits
import Definitions.Def_FineGrainedEF_Main_ScaledArith
import Definitions.Def_FineGrainedEF_Main_FFTMul
import Definitions.Def_FineGrainedEF_Main_Checks

namespace FineGrainedEF.Main

/-- Theorem A.2 (Main theorem), p. 54, both parts, complete size bound.
(i) There are constants `C, k` such that for every `n ≥ 1`, every well-formed context `Γ` and all
unsigned `n`-bit words `x, y, z` of `Γ`, the expanded context obtained by adding to `Γ` the gate
definitions of `FFTMul(x, ADD(y, z))`, `ADD(FFTMul(x, y), FFTMul(x, z))`, `FFTMul(FFTMul(x, y), z)`,
`FFTMul(x, FFTMul(y, z))`, `FFTMul(x, y)`, `FFTMul(y, x)` (parameters `N, L, p, t` fixed by `n`;
identical sub-circuits shared) and of the three output-equality checks `EQ` (outputs zero-padded to a
common length) has an EF derivation asserting the three checks, and the number of conclusion gates
plus the number of EF steps is at most `C · n · (log₂(n+2))^k`.
(ii) There is `C'` such that likewise for `ADD(ADD(x, y), z) = ADD(x, ADD(y, z))` and
`ADD(x, y) = ADD(y, x)` with total size at most `C' · n`. -/
theorem theorem_A_2 :
    (∃ C k : ℕ, ∀ (n : ℕ) (Γ : Ctx) (x y z : List ℕ),
      1 ≤ n → Γ.WF → x.length = n → y.length = n → z.length = n → Γ.HasWires (x ++ y ++ z) →
      ∃ S : ℕ,
        BigStep Γ
          (do let yz ← ADD y z
              let l₁ ← fftMul (paperParams n) x yz
              let xy ← fftMul (paperParams n) x y
              let xz ← fftMul (paperParams n) x z
              let r₁ ← ADD xy xz
              let e₁ ← eqBits l₁ r₁
              let l₂ ← fftMul (paperParams n) xy z
              let y_z ← fftMul (paperParams n) y z
              let r₂ ← fftMul (paperParams n) x y_z
              let e₂ ← eqBits l₂ r₂
              let yx ← fftMul (paperParams n) y x
              let e₃ ← eqBits xy yx
              pure [e₁, e₂, e₃]) S ∧
        S + Build.gates
          (do let yz ← ADD y z
              let l₁ ← fftMul (paperParams n) x yz
              let xy ← fftMul (paperParams n) x y
              let xz ← fftMul (paperParams n) x z
              let r₁ ← ADD xy xz
              let e₁ ← eqBits l₁ r₁
              let l₂ ← fftMul (paperParams n) xy z
              let y_z ← fftMul (paperParams n) y z
              let r₂ ← fftMul (paperParams n) x y_z
              let e₂ ← eqBits l₂ r₂
              let yx ← fftMul (paperParams n) y x
              let e₃ ← eqBits xy yx
              pure [e₁, e₂, e₃]) Γ
          ≤ C * n * Nat.log 2 (n + 2) ^ k) ∧
    (∃ C' : ℕ, ∀ (n : ℕ) (Γ : Ctx) (x y z : List ℕ),
      1 ≤ n → Γ.WF → x.length = n → y.length = n → z.length = n → Γ.HasWires (x ++ y ++ z) →
      ∃ S : ℕ,
        BigStep Γ
          (do let xy ← ADD x y
              let l₁ ← ADD xy z
              let yz ← ADD y z
              let r₁ ← ADD x yz
              let e₁ ← eqBits l₁ r₁
              let yx ← ADD y x
              let e₂ ← eqBits xy yx
              pure [e₁, e₂]) S ∧
        S + Build.gates
          (do let xy ← ADD x y
              let l₁ ← ADD xy z
              let yz ← ADD y z
              let r₁ ← ADD x yz
              let e₁ ← eqBits l₁ r₁
              let yx ← ADD y x
              let e₂ ← eqBits xy yx
              pure [e₁, e₂]) Γ
          ≤ C' * n) := by sorry

end FineGrainedEF.Main
