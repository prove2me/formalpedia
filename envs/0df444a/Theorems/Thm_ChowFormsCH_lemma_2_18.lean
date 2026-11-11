-- Prove2me | Theorems.Thm_ChowFormsCH_lemma_2_18
-- name    : ChowFormsCH.lemma_2_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:58:48.38335+00:00
-- url     : https://prove2.me/theorems/fe198691-9f17-4157-89e8-fbb407bf6566
-- title:
--   Lemma 2.18 — a polylogtime-uniform TC$^0$ family lifts a factor $Q$ of $P(y,0,\dots,0)$ to the factor $R'$ of $P$
-- statement:
--   There is a polylogtime-uniform family of TC$^0$ circuits, indexed by $(d,m,e,k,h)$, such that:
--
--   1. the circuit takes as input the $\binom{d+m+1}{d}\binom{e+k}{e}$ integer coefficients of $P\in\mathbb Z[w_1,\dots,w_k][y,x_1,\dots,x_m]$ of degree at most $e$ in $w$ and at most $d$ in $(y,x)$, and the $(d+1)\binom{e+k}{k}$ integer coefficients of $Q\in\mathbb Z[w_1,\dots,w_k][y]$ of degree at most $e$ in $w$ and at most $d$ in $y$, all of height at most $h$;
--   2. it computes $\binom{d+m+1}{d}\binom{e+k}{e}$ integers representing a polynomial $R$ of degree at most $d$ in $(y,x)$ and at most $e$ in $w$;
--   3. suppose the leading term of $P$ in $y$ lies in $\mathbb Z$, both $P$ and $P(y,0,\dots,0)$ are squarefree, and $Q$ divides $P(y,0,\dots,0)$. If $R'$ is a factor of $P$ in $\mathbb Q[w_1,\dots,w_k][y,x_1,\dots,x_m]$ such that $R'(y,0,\dots,0)$ is a nonzero $\mathbb Q$-multiple of $Q$, then $R$ is a nonzero $\mathbb Q$-multiple of $R'$.
--
--   In Theorem 4.9 this lifts the factor of the geometric resolution that survives the pruning back to the Chow form of the equidimensional component.
--
--   **Formalization Note** Inputs and outputs follow the fixed layouts of `liftOutputPoly`; the output width is chosen by the family and computable from the index. "Leading term of $P$ in $y$ lies in $\mathbb Z$": for $D$ the $y$-degree of $P$, the terms of $y$-degree at least $D$ reduce to $c\,y^D$ with $c$ a nonzero integer. The source's remark "using Gauss' lemma we can deduce …" is not a hypothesis.
--
--   Differences from the source:
--   - encoding: a family indexed by the polynomial shape, integers of unspecified bit length → index (d, m, e, k, h) with every input integer of height at most h; reason: the bit length of the inputs is implicit in the source; making it an index fixes the input count
--   - reading: an m-variate polynomial R of degree at most d in y, x₁, …, x_m and at most e in w₁, …, w_k → a polynomial R in w, y, x with those degree bounds; reason: the output count C(d+m+1, d)·C(e+k, e) and the degree bounds describe a polynomial in w, y, x
--   - reading: R′(y, 0, …, 0) is a ℚ-multiple of Q; R is a ℚ-multiple of R′ → nonzero ℚ-multiples; reason: with the zero multiple the constant-0 circuit would satisfy the claim
--   - reading: P and P(y, 0, …, 0) squarefree, Q divides P(y, 0, …, 0), R′ a factor of P in ℚ(w)[y, x] lying in ℚ[w][y, x] → squarefreeness, divisibility and R′ ∣ P in ℚ[w, y, x]; reason: the leading y-coefficient of P is a nonzero constant, so the notions agree with those over ℚ(w); the source places the factors in ℚ[w][y, x]
--   - reading: decided in time polynomial in log(s) + log(k) + Σ log(nᵢ) → time polynomial in the binary lengths of s, k and the nᵢ (each nᵢ counting at least one bit); reason: with ⌊log₂⌋, entries 0 or 1 contribute nothing and a sequential machine could not read the index
--   - encoding: TC⁰ (not defined in the paper) → polylogtime-uniform, depth bounded by one constant, size ≤ c·(number of input bits + 2)^c; reason: the standard meaning of uniform TC⁰ with the paper's uniformity
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Lemma 2.18, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_ChowFormsCH_PolylogtimeUniform
import Definitions.Def_ChowFormsCH_liftOutputPoly

set_option autoImplicit false

namespace ChowFormsCH

/-- **Lemma 2.18** (Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric computations in CH
via Chow forms*, arXiv:2611.05289, held version, sha256 75e796c6…, p.18). There exists a
polylogtime-uniform family of TC⁰ circuits such that: the circuit takes as input the
`C(d+m+1, d)·C(e+k, e)` integer coefficients of `P ∈ ℤ[w₁, …, w_k][y, x₁, …, x_m]` of degree at most
`e` in `w` and at most `d` in `(y, x)`, and the `(d+1)·C(e+k, k)` integer coefficients of
`Q ∈ ℤ[w₁, …, w_k][y]` of degree at most `e` in `w` and at most `d` in `y`; it computes
`C(d+m+1, d)·C(e+k, e)` integers representing a polynomial `R` of degree at most `d` in `(y, x)` and at
most `e` in `w`; and: suppose the leading term of `P` in `y` lies in `ℤ`, both `P` and `P(y, 0, …, 0)`
are squarefree, and `Q` divides `P(y, 0, …, 0)`; if `R′` is a factor of `P` (in
`ℚ[w₁, …, w_k][y, x₁, …, x_m]`) such that `R′(y, 0, …, 0)` is a `ℚ`-multiple of `Q`, then the computed
`R` is a `ℚ`-multiple of `R′`.

**Formalization Note** The family is indexed by `(d, m, e, k, h)`, `h` the height bound of the input
integers (implicit in the paper); inputs and outputs follow the fixed layouts `liftInput`,
`liftOutputPoly` (output width `wOut` chosen by the family, computable from the index). The source's
"an m-variate polynomial R" is the polynomial in `w, y, x` that its output count and degree bounds
describe. "The leading term of `P` in `y` lies in `ℤ`": for `D` the degree of `P` in `y`, the terms of
`P` of `y`-degree at least `D` reduce to `c·y^D` with `c` a nonzero integer. Squarefreeness and
divisibility are in `ℚ[w, y, x]` (for `P` with constant leading `y`-coefficient this agrees with
`ℚ(w)[y, x]`). Both `ℚ`-multiples are read with nonzero scalars. The sentence "using Gauss' lemma we
can deduce …" of the source is a remark and is not a hypothesis. -/
theorem lemma_2_18 :
    ∃ (Fam : List ℕ → ThresholdCircuit) (wOut : List ℕ → ℕ),
      IsUniformTC0 Fam ∧ PolyComputableIndexFn Fam (fun ι => [wOut ι]) ∧
      ∀ (d m e k h : ℕ),
        (Fam [d, m, e, k, h]).numIn = liftInputLength k m d e h ∧
        (Fam [d, m, e, k, h]).numOut =
          (expList (m + 1) d).length * (expList k e).length * (wOut [d, m, e, k, h] + 1) ∧
        ∀ (pc : Fin (expList (m + 1) d).length → Fin (expList k e).length → ℤ)
          (qc : Fin (d + 1) → Fin (expList k e).length → ℤ),
          (∀ β γ, |pc β γ| ≤ 2 ^ h) → (∀ i γ, |qc i γ| ≤ 2 ^ h) →
          (∃ (c : ℤ) (D : ℕ), c ≠ 0 ∧
              (liftPoly k m d e pc).coeff (Finsupp.single (Sum.inr 0) D) = c ∧
              ∀ μ : Fin k ⊕ Fin (m + 1) →₀ ℕ, D ≤ μ (Sum.inr 0) →
                μ ≠ Finsupp.single (Sum.inr 0) D → (liftPoly k m d e pc).coeff μ = 0) →
          Squarefree (liftPoly k m d e (fun β γ => (pc β γ : ℚ))) →
          Squarefree (MvPolynomial.aeval
              (Sum.elim (fun i : Fin k => (MvPolynomial.X (Sum.inl i) :
                  MvPolynomial (Fin k ⊕ Fin (m + 1)) ℚ))
                (fun j : Fin (m + 1) => if j = 0 then MvPolynomial.X (Sum.inr 0) else 0))
              (liftPoly k m d e (fun β γ => (pc β γ : ℚ)))) →
          liftQPoly k m d e (fun i γ => (qc i γ : ℚ)) ∣
            MvPolynomial.aeval
              (Sum.elim (fun i : Fin k => (MvPolynomial.X (Sum.inl i) :
                  MvPolynomial (Fin k ⊕ Fin (m + 1)) ℚ))
                (fun j : Fin (m + 1) => if j = 0 then MvPolynomial.X (Sum.inr 0) else 0))
              (liftPoly k m d e (fun β γ => (pc β γ : ℚ))) →
          ∀ R' : MvPolynomial (Fin k ⊕ Fin (m + 1)) ℚ,
            R' ∣ liftPoly k m d e (fun β γ => (pc β γ : ℚ)) →
            (∃ c : ℚ, c ≠ 0 ∧
              MvPolynomial.aeval
                (Sum.elim (fun i : Fin k => (MvPolynomial.X (Sum.inl i) :
                    MvPolynomial (Fin k ⊕ Fin (m + 1)) ℚ))
                  (fun j : Fin (m + 1) => if j = 0 then MvPolynomial.X (Sum.inr 0) else 0)) R'
                = c • liftQPoly k m d e (fun i γ => (qc i γ : ℚ))) →
            ∃ c' : ℚ, c' ≠ 0 ∧
              MvPolynomial.map (Int.castRingHom ℚ)
                (liftOutputPoly k m d e (wOut [d, m, e, k, h])
                  ((Fam [d, m, e, k, h]).output fun i => (liftInput k m d e h pc qc).getD i false))
                = c' • R' := by sorry

end ChowFormsCH
