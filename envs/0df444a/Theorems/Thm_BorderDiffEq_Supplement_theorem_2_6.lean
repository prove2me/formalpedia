-- Prove2me | Theorems.Thm_BorderDiffEq_Supplement_theorem_2_6
-- name    : BorderDiffEq.Supplement.theorem_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:57:43.50337+00:00
-- url     : https://prove2.me/theorems/5ddc06f3-bc9e-4412-8d25-fea44c23cff4
-- title:
--   Theorem 2.6 — explicit hitting sets for borders of sums of powers (Table 3)
-- statement:
--   Let $F$ be a field of characteristic zero, $n\ge2$ and $k,d\ge1$. For each class $\mathcal D$ below there is an explicit hitting set for the $n$-variate polynomials of degree at most $d$ in $\overline{\Sigma^{[k]}\wedge\mathcal D}$, of the stated size, constructible in time bounded by the same expression. Here $W=(2w)^{ck^2}$ for a suitable absolute constant $c$ and $\eta=\log n/\max\{1,\log\log n-\log\log W\}$:
--   1. degree at most $\delta$: $(d+1)(n+k^2\delta)^{O(k^2\delta)}$;
--   2. partial derivative space of dimension at most $\lambda$: $(nd\lambda)^{O(k^2)}$;
--   3. $\mathrm{roABP}_\pi(w,R)$, one order $\pi$ for all bases: $(d+1)(n+k)^{O(k)}\cdot\mathrm{poly}(k^2R,(nW)^\eta)$;
--   4. polynomials in $\mathrm{roABP}_\pi(w,R)$ for every order $\pi$: $(d+1)(n+k)^{O(k)}\cdot(nk^2RW)^{O(\log\log W)}$.
--
--   Precisely: for each row there are absolute constants ($c$ and $C$) and one finite multi-stack Turing machine that, on the parameters of the row written in binary (for row 3 also $\pi$), halts within $t$ steps and outputs a list $H\subseteq\mathbb Q^n$ with $|H|\le B$, where $B$ is the row's expression with $X^{O(g)}=X^{Cg}$, $\mathrm{poly}(a,b)=(a+b+1)^C$, $O(\log\log W)=C\max\{1,\log\log W\}$, $\log=\log_2$, and with bases $nd\lambda+1$ and $nk^2RW+1$ in rows 2 and 4; $H$ hits every nonzero polynomial of degree at most $d$ in the border class over every field of characteristic zero; and
--   $$
--   t\ \le\ B\cdot\bigl(L+\log_2B+2\bigr)^C,
--   $$
--   $L$ the length of the input.
--
--   The first two rows have polynomial size for constant $k$ (and $\delta$), the last two quasipolynomial size.
--
--   **Formalization Note** The machine model is the published `HMBinPacking.OutputsWithin` (Mathlib's `TM2OutputsInTime` with Boolean alphabets), the input code `HSSym.encodeInput`, the decoding `HSSym.decodeOutput`, the hitting condition `RatHits`; the partial derivative condition is the published `hasBoundedPartials`.
--
--   Differences from the source:
--   - reading: "constructed in time bounded by the same expression" (no machine model fixed) → one finite multi-stack Turing machine with Boolean input and output alphabets (`Turing.TM2ComputableAux Bool Bool`) per row; $t\le B\cdot(L+\log_2B+2)^C$ steps, $L$ the input length; reason: a bit-level machine must read its input and write numbers of $\Theta(\log B)$ bits (the $d+1$ interpolation nodes alone need $\Theta(\log d)$ bits each), so the time is the stated expression up to a factor polynomial in these bit lengths; the size bound $|H|\le B$ is literal
--   - reading: hitting set for the class $\mathrm{roABP}_\pi(w,R)$ (row 3) → the machine also reads $\pi$; reason: the class is defined by $\pi$, like $w$ and $R$; the any-order row 4 does not read $\pi$
--   - reading: $(nd\lambda)^{O(k^2)}$ and $(nk^2RW)^{O(\log\log W)}$ → bases $nd\lambda+1$ and $nk^2RW+1$; reason: the base mission's convention $X^{O(g)}=(X+1)^{Cg}$; it keeps the expression positive at $\lambda=0$ and $R=0$ (at $R=0$ the class contains the constant $1$, which needs one point)
--   - generalization: a hitting set in $F^n$ for the fixed field $F$ → one set of rational points for every field of characteristic zero; reason: $\mathbb Q\subseteq F$
--   - generalization: border constants in $F(\epsilon)$ and $f+\epsilon g$ with $g\in F[\epsilon][x]$ → constants in $F((\epsilon))$ and $f+\epsilon S$ with $S\in F[[\epsilon]][x]$ (the published `IsEpsApprox`); reason: $F(\epsilon)\subset F((\epsilon))$ and $F[\epsilon]\subset F[[\epsilon]]$, so every presentation of the paper is one here; the statement covers the paper's
--   - encoding: sums of $k$ terms → sums of at most $k$ terms; reason: every class used contains $0$ and $0^1=0$, so padding with zero terms gives the same class
--   - encoding: $O(\cdot)$, $\mathrm{poly}(\cdot)$, $c$, $\log$ → absolute constants per row, $\log=\log_2$, $O(\log\log W)=C\max\{1,\log\log W\}$; reason: reading of the asymptotic notation
--   - encoding: partial derivative space of dimension at most $\lambda$ → the published `hasBoundedPartials`; reason: Definition 4.18; same condition
--   - encoding: variables $x_1,\dots,x_n$ → `Fin n` (0-indexed); reason: Lean convention; same instances
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Theorem 2.6 and Table 3, p.9; proof §7.2 (Theorem 7.6, Fact 7.4, Lemma 7.3), pp.53–55

import Mathlib
import Definitions.Def_BorderDiffEq_Supplement_InBorderSumPow
import Definitions.Def_DerivationHitting_Commutative_PolynomialData
import Definitions.Def_BorderDiffEq_Supplement_InRoABP
import Definitions.Def_BorderDiffEq_Supplement_HSSym
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_BorderDiffEq_Supplement_RatHits

namespace BorderDiffEq.Supplement

open BorderDiffEq
open DerivationHitting.Commutative (hasBoundedPartials)

/-- **Theorem 2.6 (hitting sets for borders of sums of powers)** (Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of Structured Algebraic Circuits
via Differential Equations*, manuscript (STOC 2027 submission), Theorem 2.6 and Table 3,
p.9; proof §7.2, pp.53–55). Let `n ≥ 2` and `k, d ≥ 1` be integers. For each class `D` in Table 3,
there is an explicit hitting set for the `n`-variate polynomials of degree at most `d` in
`cl(Σ^{[k]} ∧ D)`, of the stated size, which can be constructed in time bounded by the same
expression, where `W := (2w)^{ck²}` for a suitable absolute constant `c` and
`η := log n / max{1, log log n − log log W}`:
1. degree at most `δ`: `(d + 1)(n + k²δ)^{O(k²δ)}`;
2. partial derivative space of dimension at most `λ`: `(ndλ)^{O(k²)}`;
3. `roABP_π(w, R)`, one order `π` for all bases: `(d + 1)(n + k)^{O(k)} · poly(k²R, (nW)^η)`;
4. polynomials in `roABP_π(w, R)` for every order `π`: `(d + 1)(n + k)^{O(k)} · (nk²RW)^{O(log log W)}`.

**Formalization Note.** Each row is one finite multi-stack Turing machine with Boolean alphabets
(the published `HMBinPacking.OutputsWithin`, i.e. Mathlib's `TM2OutputsInTime`) for all
parameters of that row: on the bit code of the parameters (`HSSym.encodeInput`) (row 3 also reads `π`, the class
being defined by it) it halts within `t` steps and its output decodes to at most `B` points of
`ℚⁿ` that hit every nonzero polynomial of degree at most `d` in the border, over every field of
characteristic zero; `B` is the row's expression. Each `O(·)` and `poly(·)` is one absolute
constant `C` per row (`X^{O(g)} = X^{C·g}`, `poly(a, b) = (a + b + 1)^C`,
`O(log log W) = C·max{1, log log W}`), `c` is absolute, `log = log₂`; in rows 2 and 4 the base of
the power is `ndλ + 1`, `nk²RW + 1` (the expression must stay positive at `λ = 0`, `R = 0`).
"Time bounded by the same expression" is read in this bit-level machine as
`t ≤ B · (L + log₂ B + 2)^C`, `L` the length of the input: a factor polynomial in the bit lengths
of the input and of the numbers written, which a bit-level machine must read and write. The condition `∂dim P ≤ λ` is the published `DerivationHitting.Commutative.hasBoundedPartials P λ`:
the rank over `F((ε))` of the span of all iterated partial derivatives of `P`, order `0` included
(Definition 4.18). -/
theorem theorem_2_6 :
    -- row 1: bases of degree at most δ
    (∃ C : ℕ, ∃ M : Turing.TM2ComputableAux Bool Bool,
      ∀ n k d δ : ℕ, 2 ≤ n → 1 ≤ k → 1 ≤ d →
      ∃ (out : List Bool) (t : ℕ),
        HMBinPacking.OutputsWithin M (HSSym.encodeInput [n, k, d, δ]) out t ∧
        t ≤ (d + 1) * (n + k ^ 2 * δ) ^ (C * k ^ 2 * δ) *
          ((HSSym.encodeInput [n, k, d, δ]).length +
            Nat.log 2 ((d + 1) * (n + k ^ 2 * δ) ^ (C * k ^ 2 * δ)) + 2) ^ C ∧
        (HSSym.decodeOutput n out).length ≤ (d + 1) * (n + k ^ 2 * δ) ^ (C * k ^ 2 * δ) ∧
        ∀ (F : Type) [Field F] [CharZero F], RatHits F (HSSym.decodeOutput n out) fun f =>
          f.totalDegree ≤ d ∧ InBorderSumPow F n k (fun P => P.totalDegree ≤ δ) f) ∧
    -- row 2: bases whose partial derivative space has dimension at most λ
    (∃ C : ℕ, ∃ M : Turing.TM2ComputableAux Bool Bool,
      ∀ n k d lam : ℕ, 2 ≤ n → 1 ≤ k → 1 ≤ d →
      ∃ (out : List Bool) (t : ℕ),
        HMBinPacking.OutputsWithin M (HSSym.encodeInput [n, k, d, lam]) out t ∧
        t ≤ (n * d * lam + 1) ^ (C * k ^ 2) *
          ((HSSym.encodeInput [n, k, d, lam]).length +
            Nat.log 2 ((n * d * lam + 1) ^ (C * k ^ 2)) + 2) ^ C ∧
        (HSSym.decodeOutput n out).length ≤ (n * d * lam + 1) ^ (C * k ^ 2) ∧
        ∀ (F : Type) [Field F] [CharZero F], RatHits F (HSSym.decodeOutput n out) fun f =>
          f.totalDegree ≤ d ∧ InBorderSumPow F n k (fun P => hasBoundedPartials P lam) f) ∧
    -- row 3: bases in roABP_π(w, R), one order π for all bases
    (∃ (c C : ℕ) (M : Turing.TM2ComputableAux Bool Bool),
      ∀ (n k d w R : ℕ) (π : Equiv.Perm (Fin n)), 2 ≤ n → 1 ≤ k → 1 ≤ d →
      ∃ (out : List Bool) (t : ℕ),
        HMBinPacking.OutputsWithin M
          (HSSym.encodeInput ([n, k, d, w, R] ++ List.ofFn fun i => ((π i : Fin n) : ℕ))) out t ∧
        (t : ℝ) ≤ ((d + 1 : ℝ) * ((n + k : ℝ) ^ (C * k)) *
            ((k ^ 2 * R : ℝ) + ((n * (2 * w) ^ (c * k ^ 2) : ℕ) : ℝ) ^ (Real.logb 2 n /
              max 1 (Real.logb 2 (Real.logb 2 n) -
                Real.logb 2 (Real.logb 2 (((2 * w) ^ (c * k ^ 2) : ℕ) : ℝ)))) + 1) ^ C) *
          (((HSSym.encodeInput ([n, k, d, w, R] ++ List.ofFn fun i => ((π i : Fin n) : ℕ))).length +
            Nat.log 2 ⌈(d + 1 : ℝ) * ((n + k : ℝ) ^ (C * k)) *
              ((k ^ 2 * R : ℝ) + ((n * (2 * w) ^ (c * k ^ 2) : ℕ) : ℝ) ^ (Real.logb 2 n /
                max 1 (Real.logb 2 (Real.logb 2 n) -
                  Real.logb 2 (Real.logb 2 (((2 * w) ^ (c * k ^ 2) : ℕ) : ℝ)))) + 1) ^ C⌉₊ +
              2 : ℕ) : ℝ) ^ C ∧
        ((HSSym.decodeOutput n out).length : ℝ) ≤ (d + 1 : ℝ) * ((n + k : ℝ) ^ (C * k)) *
            ((k ^ 2 * R : ℝ) + ((n * (2 * w) ^ (c * k ^ 2) : ℕ) : ℝ) ^ (Real.logb 2 n /
              max 1 (Real.logb 2 (Real.logb 2 n) -
                Real.logb 2 (Real.logb 2 (((2 * w) ^ (c * k ^ 2) : ℕ) : ℝ)))) + 1) ^ C ∧
        ∀ (F : Type) [Field F] [CharZero F], RatHits F (HSSym.decodeOutput n out) fun f =>
          f.totalDegree ≤ d ∧ InBorderSumPow F n k (InRoABP (LaurentSeries F) n π w R) f) ∧
    -- row 4: bases in roABP_π(w, R) for every order π
    (∃ (c C : ℕ) (M : Turing.TM2ComputableAux Bool Bool),
      ∀ n k d w R : ℕ, 2 ≤ n → 1 ≤ k → 1 ≤ d →
      ∃ (out : List Bool) (t : ℕ),
        HMBinPacking.OutputsWithin M (HSSym.encodeInput [n, k, d, w, R]) out t ∧
        (t : ℝ) ≤ ((d + 1 : ℝ) * ((n + k : ℝ) ^ (C * k)) *
            (((n * k ^ 2 * R * (2 * w) ^ (c * k ^ 2) : ℕ) : ℝ) + 1) ^
              ((C : ℝ) * max 1 (Real.logb 2 (Real.logb 2 (((2 * w) ^ (c * k ^ 2) : ℕ) : ℝ))))) *
          (((HSSym.encodeInput [n, k, d, w, R]).length +
            Nat.log 2 ⌈(d + 1 : ℝ) * ((n + k : ℝ) ^ (C * k)) *
              (((n * k ^ 2 * R * (2 * w) ^ (c * k ^ 2) : ℕ) : ℝ) + 1) ^
                ((C : ℝ) * max 1 (Real.logb 2 (Real.logb 2 (((2 * w) ^ (c * k ^ 2) : ℕ) : ℝ))))⌉₊ +
              2 : ℕ) : ℝ) ^ C ∧
        ((HSSym.decodeOutput n out).length : ℝ) ≤ (d + 1 : ℝ) * ((n + k : ℝ) ^ (C * k)) *
            (((n * k ^ 2 * R * (2 * w) ^ (c * k ^ 2) : ℕ) : ℝ) + 1) ^
              ((C : ℝ) * max 1 (Real.logb 2 (Real.logb 2 (((2 * w) ^ (c * k ^ 2) : ℕ) : ℝ)))) ∧
        ∀ (F : Type) [Field F] [CharZero F], RatHits F (HSSym.decodeOutput n out) fun f =>
          f.totalDegree ≤ d ∧
            InBorderSumPow F n k (fun P => ∀ π : Equiv.Perm (Fin n),
              InRoABP (LaurentSeries F) n π w R P) f) := by sorry

end BorderDiffEq.Supplement
