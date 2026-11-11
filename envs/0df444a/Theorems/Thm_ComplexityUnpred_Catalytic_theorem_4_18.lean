-- Prove2me | Theorems.Thm_ComplexityUnpred_Catalytic_theorem_4_18
-- name    : ComplexityUnpred.Catalytic.theorem_4_18
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:05:18.184239+00:00
-- url     : https://prove2.me/theorems/9bde57da-8f79-4062-a199-bdbb4f25482d
-- title:
--   Theorem 4.18 — LossyCoding families with a poly-time compressor and a poly-time inplaceFL decompressor reduce to WeakExcess
-- statement:
--   Let $n:\{0,1\}^*\to\mathbb N$ and let $(C_x,D_x)_{x\in\{0,1\}^*}$ be a family of LossyCoding instances, $C_x:\{0,1\}^{n(x)}\to\{0,1\}^{n(x)-1}$, $D_x:\{0,1\}^{n(x)-1}\to\{0,1\}^{n(x)}$, such that
--
--   1. $n$ is computable in polynomial time and polynomially bounded;
--   2. a polynomial-time Turing machine computes $C_x(y)$ from $x$ and $y\in\{0,1\}^{n(x)}$;
--   3. a polynomial-time inplaceFL machine with read-only advice $x$ and read-write input $y\in\{0,1\}^{n(x)}$ computes $D^{\mathrm{ext}}_x(y)=D_x(y_{<n(x)})$, in time polynomial and work space logarithmic in $|x|$.
--
--   Then
--   $$\text{LossyCoding on }(C_x,D_x)_x\ \le_P\ \textsf{WeakExcess}.$$
--
--   **Formalization Note** Condition 1 is `PolyTimeComputable` of $x\mapsto1^{n(x)}$ plus `PolyBoundedStr n`; condition 2 is `PairPolyTime n C`; condition 3 is `InPlaceFLPoly n (fun x => Dext (D x))`, the published catalytic machine with the advice on its input tape and $y$ on its (non-restored) catalytic tape.
--
--   Differences from the source:
--   - encoding: n : {0,1}* → N, where N = {1, 2, …} by §2.1 (p. 17) → hypothesis ∀ x, 1 ≤ n x; reason: Lean ℕ includes zero; the explicit positivity clause expresses the source domain convention without adding a hypothesis or conclusion
--   - encoding: n computable in polynomial time → CookPvsNP.PolyTimeComputable (fun x => 1^{n(x)}) (unary output); reason: for a polynomially bounded n, unary and binary output are computable from each other in polynomial time
--   - encoding: polynomially bounded: f(N) ≤ poly(N) → f N ≤ N^k + k for some k; reason: every polynomial is bounded by N^k + k for some k
--   - encoding: polynomial-time TM computing C_x(y) from x and y → PairPolyTime: a polynomial-time Cook machine maps the tagged pair (x, y) to C_x(y) for every y ∈ {0,1}^{n(x)}; reason: the platform's pair convention and polynomial time
--   - encoding: polynomial-time inplaceFL TM with read-only advice x and read-write input y computing D^ext_x(y) → InPlaceFLPoly: the published catalytic machine with x on the read-only input tape and y on the catalytic tape (not restored), halting within C(|x|+2)^k steps with D^ext_x(y) there, at most C(⌊log₂(|x|+2)⌋+1) visited binary work cells; reason: efficiency in |x| as the paper says (p. 34); binary work alphabet costs a constant factor in space
--   - encoding: ≤P: both maps computable in deterministic polynomial time → CardinalMatching.SearchReduces with CookPvsNP.PolyTimeComputable (one-tape Cook machines, time |x|^k + k); the solution map reads the tagged pair (x, y); reason: the published platform reduction; it requires correctness for every answer, as §2.2 does
--   - encoding: WeakExcess instance: n, ℓ in unary, circuit C, ind as an explicit table → WeakExcessInstance.encode (unary n, ℓ; circuit code; 2^ℓ table entries in lexicographic label order, 1-based, binary); reason: one concrete binary code of the paper's input
--   - encoding: answer: out-degree ≥ in-degree in the hidden deterministic hypercube digraph G with EdgeExists = C → out-degree ≥ in-degree in HypercubeDigraph.ofOracle ind C; reason: every such G has the same non-self-loop edges as ofOracle ind C, and self-loops do not change out − in, so the answer set is the same
--   - reading: THRESHOLD gates with unspecified thresholds → gates Th_t (at least t inputs are 1), t in the gate label; reason: the paper does not fix the thresholds; Th_t is the standard reading and keeps the gate in the basis
-- source:
--   Agarwala, Dorfman, The Complexity of Unpredictability, arXiv:2611.05956v1, p. 37, Theorem 4.18

import Mathlib
import Definitions.Def_CardinalMatching_SearchReduces
import Definitions.Def_ComplexityUnpred_Catalytic_WeakExcess
import Definitions.Def_ComplexityUnpred_Catalytic_LossyFamily

namespace ComplexityUnpred.Catalytic

/-- **Theorem 4.18** (Agarwala, Dorfman, arXiv:2611.05956v1, p. 37). Let `n : {0,1}* → ℕ` and
`(C_x, D_x)_x` be a LossyCoding family with `C_x : {0,1}^{n(x)} → {0,1}^{n(x)−1}` and
`D_x : {0,1}^{n(x)−1} → {0,1}^{n(x)}` such that (1) `n` is polynomial-time computable and
polynomially bounded, (2) `(x, y) ↦ C_x(y)` is polynomial-time computable, (3) a polynomial-time
`inplaceFL` machine with read-only advice `x` and read-write input `y ∈ {0,1}^{n(x)}` computes
`D^ext_x(y)`. Then LossyCoding on `(C_x, D_x)_x ≤_P WeakExcess`. -/
theorem theorem_4_18 (n : List Bool → ℕ)
    (C : (x : List Bool) → (Fin (n x) → Bool) → Fin (n x - 1) → Bool)
    (D : (x : List Bool) → (Fin (n x - 1) → Bool) → Fin (n x) → Bool)
    (hpos : ∀ x, 1 ≤ n x)
    (hn : CookPvsNP.PolyTimeComputable (fun x : List Bool => List.replicate (n x) true) ∧
      PolyBoundedStr n)
    (hC : PairPolyTime n C)
    (hD : InPlaceFLPoly n (fun x => Dext (D x))) :
    CardinalMatching.SearchReduces (LossyCodingFamily n C D) WeakExcess := by sorry

end ComplexityUnpred.Catalytic
