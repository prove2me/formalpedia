-- Prove2me | Theorems.Thm_ComplexityUnpred_Catalytic_theorem_4_19
-- name    : ComplexityUnpred.Catalytic.theorem_4_19
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:05:39.065202+00:00
-- url     : https://prove2.me/theorems/f945f6cc-d50d-42ed-abf1-262a0a835faa
-- title:
--   Theorem 4.19 (Theorem 3.1 of [CLMP25]) — FastCatTape(M, p_M) reduces to a LossyCoding family of the kind Theorem 4.18 handles
-- statement:
--   Let $M$ be a catalytic logspace machine which, on inputs of length $n$, uses $p(n)$ catalytic space. Then there exist a logspace-computable polynomially bounded $p_M:\mathbb N\to\mathbb N$ and a family of LossyCoding instances $(C_x,D_x)_{x\in\{0,1\}^*}$ such that
--
--   1. $C_x:\{0,1\}^{n(x)}\to\{0,1\}^{n(x)-1}$ and $D_x:\{0,1\}^{n(x)-1}\to\{0,1\}^{n(x)}$, where $n$ is polynomially bounded and logspace computable;
--   2. a polynomial-time Turing machine computes $C_x(y)$ from $x$ and $y\in\{0,1\}^{n(x)}$;
--   3. a polynomial-time inplaceFL machine with read-only advice $x$ and read-write input $y\in\{0,1\}^{n(x)}$ computes $D^{\mathrm{ext}}_x(y)$;
--   4. for every $x$ and every solution $y$ to LossyCoding on $(C_x,D_x)$, the prefix $y_{\le p(|x|)}$ is a solution to FastCatTape$(M,p_M)$ on $x$:
--   $$D_x(C_x(y))\ne y\ \Longrightarrow\ |y_{\le p(|x|)}|=p(|x|)\ \text{and}\ \mathrm{time}(M(x,y_{\le p(|x|)}))\le p_M(|x|).$$
--
--   The theorem is proved by Cook, Li, Mertz and Pyne; the paper restates it in the language of in-place computation.
--
--   **Formalization Note** The machine model, "logspace computable" and the in-place machine with advice are those of the `FastCatTape` and `LossyFamily` definitions; the prefix is `List.take (p.eval |x|)`.
--
--   Differences from the source:
--   - generalization: catalytic logspace machine: catalytic space d n^d, work d log n (Definitions 2.6, 2.8, 2.10) → IsCatalyticLogspace M C p: the published binary machine, any polynomial p ∈ ℕ[X] of catalytic length, any C ≥ 1, work ≤ C(⌊log₂(|x|+2)⌋+1) visited cells; reason: contains the paper's machines (p := d X^d, C := d up to the constant-factor cost of a binary work alphabet), so the statement specializes to them
--   - reading: logspace-computable function (model not fixed) → LogspaceComputable / LogspaceComputableNat: the published machine with an empty catalytic tape, binary output (least significant bit first), O(log) visited work cells; for ℕ → ℕ, computed from any input of length N; reason: the ordinary logspace transducer; binary and unary output are interchangeable for polynomially bounded values
--   - encoding: n : {0,1}* → N, where N = {1, 2, …} by §2.1 (p. 17) → conclusion ∀ x, 1 ≤ n x; reason: Lean ℕ includes zero; the explicit positivity clause expresses the source domain convention without adding a hypothesis or conclusion
--   - encoding: polynomially bounded: f(N) ≤ poly(N) → f N ≤ N^k + k for some k; reason: every polynomial is bounded by N^k + k for some k
--   - encoding: polynomial-time TM computing C_x(y); polynomial-time inplaceFL TM with advice computing D^ext_x(y) → PairPolyTime n C; InPlaceFLPoly n (fun x => Dext (D x)), as in Theorem 4.18; reason: same conventions as Theorem 4.18
--   - encoding: strings in {0,1}ⁿ, indices in [n] = {1, …, n} → Fin n → Bool, 0-based indices Fin n; reason: Lean convention; same instances
-- source:
--   Agarwala, Dorfman, The Complexity of Unpredictability, arXiv:2611.05956v1, p. 39, Theorem 4.19 (Theorem 3.1 of [CLMP25])

import Mathlib
import Definitions.Def_ComplexityUnpred_Catalytic_FastCatTape
import Definitions.Def_ComplexityUnpred_Catalytic_LossyFamily

namespace ComplexityUnpred.Catalytic

open CatalyticMatching.General

/-- **Theorem 4.19** (Agarwala, Dorfman, arXiv:2611.05956v1, p. 39; Theorem 3.1 of
Cook–Li–Mertz–Pyne [CLMP25]). For every catalytic logspace machine `M` with catalytic space
`p(n)` there are a logspace-computable polynomially bounded `p_M : ℕ → ℕ` and a LossyCoding
family `(C_x, D_x)_x` such that (1) `C_x : {0,1}^{n(x)} → {0,1}^{n(x)−1}`,
`D_x : {0,1}^{n(x)−1} → {0,1}^{n(x)}` with `n` polynomially bounded and logspace computable,
(2) `(x, y) ↦ C_x(y)` is polynomial-time computable, (3) a polynomial-time `inplaceFL` machine
with read-only advice `x` computes `D^ext_x(y)`, (4) for every `x` and every solution `y` to
LossyCoding on `(C_x, D_x)`, `y_{≤p(|x|)}` is a solution to `FastCatTape(M, p_M)` on `x`. -/
theorem theorem_4_19 (M : Machine) (Cw : ℕ) (p : Polynomial ℕ)
    (hM : IsCatalyticLogspace M Cw p) :
    ∃ pM : ℕ → ℕ, LogspaceComputableNat pM ∧ PolyBounded pM ∧
      ∃ (n : List Bool → ℕ)
        (C : (x : List Bool) → (Fin (n x) → Bool) → Fin (n x - 1) → Bool)
        (D : (x : List Bool) → (Fin (n x - 1) → Bool) → Fin (n x) → Bool),
        (∀ x, 1 ≤ n x) ∧ PolyBoundedStr n ∧ LogspaceComputable n ∧
        PairPolyTime n C ∧ InPlaceFLPoly n (fun x => Dext (D x)) ∧
        ∀ (x : List Bool) (y : Fin (n x) → Bool), IsLossySolution (C x) (D x) y →
          (FastCatTape M p pM).answer x ((List.ofFn y).take (p.eval x.length)) := by sorry

end ComplexityUnpred.Catalytic
