-- Prove2me | Theorems.Thm_EulerSparsify_lemma_5_10
-- name    : EulerSparsify.lemma_5_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:40:03.333554+00:00
-- url     : https://prove2.me/theorems/1f4c3a29-e103-4ca7-825d-16e6f8faa9a9
-- title:
--   Lemma 5.10 — one half-sparsification step (Algorithm 5.1): degrees kept, $\mathrm{nnz}$ shrinks, error $C_{\mathrm{ESO}}\rho^{1/2}$, randomized polynomial time
-- statement:
--   Let $c_{\mathrm{ner}}>0$ be a constant for which Proposition 4.3 holds. There are universal constants $C_{\mathrm{ESO}}>0$ and $c_{\mathrm{tight}}\in(0,1)$ with the following properties.
--
--   1. **Existence.** Let $\vec G=(V,E,w)$ be a simple directed graph with nonnegative weights, $n=|V|$, $G=\mathrm{und}(\vec G)$, and let $\{K_i,F_i,b_i\}_{i\in[I]}$ be a $\rho$-nested ER partitioning of $(V,\mathrm{supp}(w),w_{\mathrm{supp}(w)})$. Then there is $x'\in[-1,1]^E$, zero outside $\mathrm{supp}(w)$, such that $w'=w\circ(\mathbf 1_E+x')$ satisfies
--      - $B^\top w'=B^\top w$;
--      - $\mathrm{nnz}(w')\le\max\bigl((1-c_{\mathrm{tight}})\mathrm{nnz}(w),\ \max\{64,2c_{\mathrm{ner}}\}n\bigr)$;
--      - $\bigl\|L_G^{\dagger/2}B^\top(W'-W)HL_G^{\dagger/2}\bigr\|_{\mathrm{op}}\le C_{\mathrm{ESO}}\,\rho^{1/2}$.
--   2. **Randomized polynomial time.** There is a polynomial $q$ and a Turing machine, polynomial time in its input length, that reads the binary encoding of $(\vec G,\{K_i,F_i,b_i\},\delta)$ (rational weights, $\delta\in(0,1)$) and $N=q(\text{encoding length})$ uniform random bits, and outputs such a $w'$ for at least a $1-\delta$ fraction of the coin strings, for every $\rho$ for which the given family is a $\rho$-nested ER partitioning.
--
--   Each round of Algorithm 5.2 applies this step; the number of edges falls geometrically while the spectral errors form a geometric series.
--
--   **Formalization Note** The hypothesis on $c_{\mathrm{ner}}$ is `NestedConst c_ner` (both clauses of Proposition 4.3).
--
--   Differences from the source:
--   - reading: c_ner (named in item 2 and line 3; the proof uses ρ = c_ner n/m̂ ≤ 1/2) → for every c_ner > 0 for which Proposition 4.3 holds (NestedConst c_ner), constants C_ESO, c_tight exist; reason: c_ner is Proposition 4.3's constant; the statement is made for every such constant, which includes the paper's
--   - reading: "with high probability" and "implementable in poly(n, log U, log 1/δ) time" → existence clause without probability, plus a randomized TM2 machine with coin strings of polynomial length succeeding for a 1 − δ fraction, δ ∈ (0,1) an input, time polynomial in the binary input length; reason: the lemma's probability concerns the random Gaussian of line 5 and the time bound names δ; a TM reads binary inputs
--   - reading: "a ρ-nested ER partitioning" (ρ unspecified) → every real ρ for which the input is ρ-nested; ρ^{1/2} = Real.sqrt ρ; reason: line 1 fixes no ρ; when line 3 fails w' = w satisfies items 1–3 for every ρ, and otherwise the proof can use whichever of the given and Proposition 4.3's partitionings has smaller quality
--   - encoding: "it returns G⃗′ = (V, E, w′)" (lines 6–9) → w' = w ∘ (1_E + x') with x' ∈ [−1,1]^E vanishing off supp(w), satisfying items 1–3; reason: lines 6–7 and 9 of Algorithm 5.1
--   - encoding: input ε ∈ (0, 1/100) → omitted; reason: Algorithm 5.1 never uses ε
--   - encoding: "simple G⃗" → no self-loops and no two edges with the same head and tail; reason: the meaning of a simple directed graph; antiparallel edges are allowed
--   - reading: Definition 2.1 → IsNestedER: j ∈ ℤ, item 4 vertex-disjoint, diam_ER(K̂_i) ≤ ρ including connectivity of K̂_i on U_i; reason: the proof of Proposition 4.3 says the K_i of a bucket are vertex disjoint and that K̂_i is connected as diam_ER ≤ ρ; ER across components is +∞
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Lemma 5.10, pp.21–22 (PDF pp.23–24), with the sentence after Algorithm 5.1

import Mathlib
import Definitions.Def_EulerSparsify_NestedConst
import Definitions.Def_EulerSparsify_DiGraph_supp
import Definitions.Def_EulerSparsify_HalfStepGood
import Definitions.Def_EulerSparsify_encHalfStepIn
import Definitions.Def_ReserveLB_encRatList
import Definitions.Def_KarpLiptonOM_countStr

namespace EulerSparsify

/-- **Lemma 5.10** (one half-sparsification step, Algorithm 5.1), pp.21–22, PDF pp.23–24.
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Lemma 5.10: "Suppose that ExistentialDecompSparsify (Algorithm 5.1) is run on inputs as
specified in Line 1. Then, it returns ⃗G′ = (V, E, w′) satisfying the following properties, with
high probability for some universal constants C_ESO, c_tight.
1. Bᵀ_⃗G w′ = Bᵀ_⃗G w.
2. nnz(w′) ≤ max((1 − c_tight)nnz(w), max{64, 2c_ner}n).
3. ‖L_G^{†/2} Bᵀ_⃗G (W′ − W) H_⃗G L_G^{†/2}‖_op ≤ C_ESO ρ^{1/2}."
Algorithm 5.1, line 1: "Input: a simple ⃗G = (V, E, w) and {K_i, F_i, b_i}_{i∈[I]} is a ρ-nested ER
partitioning of (V, supp(w), w_supp(w))"; p.22: "Moreover, ExistentialDecompSparsify is
implementable in poly(n, log U, log 1/δ) time."

For every constant `c_ner > 0` for which Proposition 4.3 holds (`NestedConst c_ner`, the constant
used in line 3 of Algorithm 5.1), there are universal constants `C_ESO > 0` and
`c_tight ∈ (0, 1)` such that:
* (existence) for every simple directed graph `⃗G` with nonnegative weights, every `ρ` and every
  `ρ`-nested ER partitioning of `(V, supp(w), w_supp(w))`, some `w' = w ∘ (1 + x')` with
  `x' ∈ [−1,1]^E` vanishing off `supp(w)` satisfies items 1–3 (`HalfStepGood`); and
* (randomized polynomial time) one Turing machine, run on the binary encoding of
  `(⃗G, partitioning, δ)` and a uniform coin string of polynomial length `N`, outputs such `w'` for at
  least a `1 − δ` fraction of the coin strings, for every rational input with `δ ∈ (0, 1)` and
  every `ρ` for which the given partitioning is `ρ`-nested.

**Formalization Note.**
* `c_ner` is Proposition 4.3's constant (item 2 and line 3 name it; the proof uses
  `ρ = c_ner · n/m̂ ≤ 1/2`), so the statement holds for every constant for which Proposition 4.3
  holds, as a hypothesis.
* "With high probability" with the time `poly(n, log U, log 1/δ)` is read as: failure probability
  at most an input `δ`, time polynomial in the binary input length (which includes `log 1/δ`).
  The existence clause has no probability.
* The unused input `ε ∈ (0, 1/100)` of Algorithm 5.1 is omitted. Edge numbers in the encoded
  partitioning index the edge list of the input; the partitioning is read with
  `NestedFamily.ofList` on the edges of nonzero weight.
* Simple: no self-loops and no two edges with the same head and tail (antiparallel edges allowed). -/
theorem lemma_5_10 :
    ∀ c_ner : ℝ, 0 < c_ner → NestedConst c_ner →
      ∃ C_ESO : ℝ, 0 < C_ESO ∧ ∃ c_tight : ℝ, 0 < c_tight ∧ c_tight < 1 ∧
        (∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
            (G : DiGraph V E), (∀ e, 0 ≤ G.w e) → G.IsSimple →
            ∀ (ρ : ℝ) (P : NestedFamily V G.suppEdges), IsNestedER G.supp ρ P →
              ∃ w' : E → ℝ, HalfStepGood c_ner C_ESO c_tight ρ G w') ∧
        ∃ (q : Polynomial ℕ)
          (alg : (RatDigraph × List (List ℕ × List ℕ × List ℕ × ℤ) × ℚ) × List Bool → List ℚ),
          Nonempty (Turing.TM2ComputableInPolyTime encHalfStepInCoins ReserveLB.encRatList alg) ∧
          ∀ (I : RatDigraph) (hI : I.WellFormed) (Pl : List (List ℕ × List ℕ × List ℕ × ℤ))
            (δ : ℚ), (I.toDiGraph hI).IsSimple → 0 < δ → δ < 1 →
            ∀ ρ : ℝ, IsNestedER (I.toDiGraph hI).supp ρ
                (NestedFamily.ofList Fin.val (fun e => (e : Fin I.2.length).val) Pl) →
              (1 - (δ : ℝ)) * 2 ^ (q.eval (encHalfStepIn (I, Pl, δ)).length) ≤
                (KarpLiptonOM.countStr (q.eval (encHalfStepIn (I, Pl, δ)).length) fun cs =>
                  (alg ((I, Pl, δ), cs)).length = I.2.length ∧
                    HalfStepGood c_ner C_ESO c_tight ρ (I.toDiGraph hI)
                      (fun e => ((alg ((I, Pl, δ), cs)).getD e.val 0 : ℝ)) : ℝ) := by sorry

end EulerSparsify
