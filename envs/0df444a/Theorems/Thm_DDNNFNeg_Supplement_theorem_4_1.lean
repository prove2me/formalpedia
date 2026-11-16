-- Prove2me | Theorems.Thm_DDNNFNeg_Supplement_theorem_4_1
-- name    : DDNNFNeg.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:50:22.391612+00:00
-- url     : https://prove2.me/theorems/d576cc5c-3e9c-4b16-8bc4-dbd271a04aa3
-- title:
--   Theorem 4.1 — a polynomial-time algorithm negating d-DNNFs would give NP = RP
-- statement:
--   Suppose there is a deterministic polynomial-time algorithm $A$ that, given (the binary encoding of) a d-DNNF $D$ over the variables $x_1, \dots, x_n$ computing a Boolean function $f$, outputs (the encoding of) a d-DNNF over the same variables computing $\neg f$. Then
--
--   $$\mathrm{NP} = \mathrm{RP}.$$
--
--   Equivalently: unless NP = RP, no polynomial-time algorithm compiles the negation of a d-DNNF into a d-DNNF. Theorem 1.1 rules out such an algorithm unconditionally; this conditional statement has a much shorter proof (a reduction from 3-CNF-SAT to the complement of polynomial identity testing). In particular the hypothesis is false (Theorem 1.1 forces exponentially large outputs on some linear-size inputs), so the implication also follows from Theorem 1.1; the paper includes Theorem 4.1, as here, for its self-contained conditional argument.
--
--   **Formalization Note** Algorithms are polynomial-time functions on binary strings (Mathlib's multi-stack Turing machines). Circuits are encoded with all numbers in binary, so the input length is polynomial in the number of variables plus the circuit size. The input d-DNNFs have literal input gates, as in the paper; the output d-DNNF may also use constant leaves; nothing is required of $A$ on inputs that are not d-DNNFs. NP and RP are the usual verifier classes (RP with one-sided error $1/2$).
--
--   Differences from the source:
--   - encoding: a polynomial-time algorithm taking and returning d-DNNFs → a function on binary strings computable in polynomial time by a Mathlib FinTM2 machine, applied to encodeNNF D and returning encodeNNF D′; reason: standard machine model and an encoding of length polynomial in n + size
--   - reading: output circuit with the same variables as the input (the paper's without-loss-of-generality convention, p.10) → input and output are NNFs over the same variable type Fin n; reason: the paper assumes this convention itself and shows it costs only polynomial time
--   - generalization: the output is a d-DNNF (literal input gates) → the output is a d-DNNF that may also use constant leaves; reason: the hypothesis becomes weaker, so the theorem becomes stronger; an algorithm as in the source satisfies it
--   - encoding: NP = RP → ∀ L ⊆ {0,1}*, InNP L ↔ InRP L, with verifier definitions over Mathlib FinTM2 polynomial time; reason: the standard definitions of the two classes
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Theorem 4.1, p.10 (proof pp.10–11)

import Mathlib
import Definitions.Def_DDNNFNeg_NNF_Computes
import Definitions.Def_DDNNFNeg_NNF_IsConstFree
import Definitions.Def_DDNNFNeg_NNF_IsDDNNF
import Definitions.Def_DDNNFNeg_Supplement_encodeNNF
import Definitions.Def_DDNNFNeg_Supplement_InNP
import Definitions.Def_DDNNFNeg_Supplement_InRP

namespace DDNNFNeg.Supplement

/-- **Theorem 4.1** (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), p.10; proof pp.10–11): there is no polynomial-time algorithm that,
given a d-DNNF computing a Boolean function `f`, constructs a d-DNNF computing `¬f`, unless
NP = RP. Stated as: if such an algorithm exists, then NP = RP.

**Formalization Note** An algorithm is a function `A` on binary strings computable in
deterministic polynomial time (Mathlib's `FinTM2` machines). It receives the binary encoding
`encodeNNF D` of a d-DNNF `D` over the variables `Fin n` (constant-free, as the paper's d-DNNFs
are) and must return the encoding of a d-DNNF `D'` over the same variables `Fin n` computing
`¬f`, where `f` is the function `D` computes. The output may use constant leaves (the paper's
proof propagates constants in it), which makes the hypothesis weaker; nothing is required of
`A` on other inputs. "Same variables" is the paper's own without-loss-of-generality convention
(p.10). NP = RP is the equality of the classes `InNP` and `InRP` of languages over `{0,1}`. -/
theorem theorem_4_1 :
    (∃ A : List Bool → List Bool, PolyTimeFun A ∧
      ∀ (n : ℕ) (D : NNF (Fin n)), D.IsConstFree → D.IsDDNNF →
        ∃ D' : NNF (Fin n), D'.IsDDNNF ∧ D'.Computes (fun x => !D.eval x D.out) ∧
          A (encodeNNF D) = encodeNNF D') →
    ∀ L : Set (List Bool), InNP L ↔ InRP L := by sorry

end DDNNFNeg.Supplement
