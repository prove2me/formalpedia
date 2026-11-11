-- Prove2me | Theorems.Thm_ChowFormsCH_lemma_2_13
-- name    : ChowFormsCH.lemma_2_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:58:28.508002+00:00
-- url     : https://prove2.me/theorems/fbd5850e-a7df-4ff1-a3cf-5ae9807749f3
-- title:
--   Lemma 2.13 — a polylogtime-uniform TC$^0$ family computes the GCD of two multivariate integer polynomials after a random shear
-- statement:
--   There is a polylogtime-uniform family of TC$^0$ circuits, indexed by $(m,d,h)$ with $m\ge 1$, such that:
--
--   1. the circuit takes as input $2\binom{d+m}{d}$ integers, the coefficients of two polynomials $f,g\in\mathbb Z[x_1,\dots,x_m]$ of degree at most $d$, and $m-1$ integers $a_2,\dots,a_m$, all of height at most $h$;
--   2. it computes $\binom{d+m}{d}$ integers representing a polynomial $h$ of degree at most $d$;
--   3. if the highest-degree parts of $f$ and $g$ depend on $x_1$, and $a_2,\dots,a_m$ are independently and uniformly sampled from a set $S$ of $b$ integers of height at most $h$, then with probability at least
--   $$
--   1-\frac{2\,m\,d^{\,m}}{b}
--   $$
--   $h$ is a greatest common divisor of $f$ and $g$ in $\mathbb Q[x_1,\dots,x_m]$, i.e. a nonzero scalar multiple of their GCD.
--
--   This multivariate GCD circuit is used in Theorem 4.9 to compute $\gcd(R_G,R_H)$.
--
--   **Formalization Note** Inputs and outputs follow the fixed layouts of `gcdOutputPoly`; the output width is chosen by the family and computable from the index within the uniformity time bound. TC$^0$ means: polylogtime-uniform, depth bounded by one constant, size polynomial in the number of input bits.
--
--   Differences from the source:
--   - encoding: a family indexed by the polynomial shape (m, d), integers of unspecified bit length → index (m, d, h) with every input integer of height at most h (|z| ≤ 2^h, sign bit and h + 1 magnitude bits); reason: the bit length of the inputs is implicit in the source; making it an index is how the circuits' input count is fixed
--   - reading: two m-variate polynomials of degree d → of degree at most d; reason: the input format, C(d+m, d) coefficients, is the dense representation of polynomials of degree at most d; this covers degree exactly d
--   - reading: h is a scalar multiple of the GCD of f and g → h is a gcd of f and g in ℚ[x] (a nonzero scalar multiple); reason: with the zero multiple the constant-0 circuit would satisfy the claim; the GCD is nonzero since f ≠ 0
--   - reading: with probability 1 − 2md^m/b, the integers sampled from a set of size b → probability at least 1 − 2md^m/b, for every set S of b ≥ 1 integers of height at most h; reason: the proof shows a lower bound; the circuit reads the sampled integers as inputs of height at most h
--   - reading: decided in time polynomial in log(s) + log(k) + Σ log(nᵢ) → time polynomial in the binary lengths of s, k and the nᵢ (each nᵢ counting at least one bit); reason: with ⌊log₂⌋, entries 0 or 1 contribute nothing and a sequential machine could not read the index; the binary-length reading is polynomial in the query length
--   - encoding: TC⁰ (not defined in the paper) → polylogtime-uniform, depth bounded by one constant, size ≤ c·(number of input bits + 2)^c; reason: the standard meaning of uniform TC⁰ with the paper's uniformity
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Lemma 2.13, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_ChowFormsCH_PolylogtimeUniform
import Definitions.Def_ChowFormsCH_gcdOutputPoly
import Definitions.Def_ChowFormsCH_IsSqfPart

set_option autoImplicit false

namespace ChowFormsCH

/-- **Lemma 2.13** (Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric computations in CH
via Chow forms*, arXiv:2611.05289, held version, sha256 75e796c6…, p.15). There exists a
polylogtime-uniform family of TC⁰ circuits such that: the circuits take as input `2·C(d+m, d)`
integers, the coefficients of two `m`-variate polynomials `f, g` of degree `d` with integer
coefficients, and `m − 1` integers `a₂, …, a_m`; they compute `C(d+m, d)` integers representing an
`m`-variate polynomial `h` of degree at most `d`; and if `a₂, …, a_m` are independently and uniformly
sampled from a set of size `b`, and the highest degree parts of `f` and `g` depend on `x₁`, then with
probability `1 − 2md^m/b` the polynomial `h` is a scalar multiple of the GCD of `f` and `g` in
`ℚ[x₁, …, x_m]`.

**Formalization Note** The family is indexed by `(m, d, h)`, `h` the height bound of the input
integers (implicit in the paper); inputs and outputs follow the fixed layouts `gcdInput` and
`gcdOutputPoly`, with the output width `wOut` chosen by the family and computable from the index.
"Of degree `d`" is read as "of degree at most `d`" (the dense input format). "Scalar multiple of the
GCD" is read with a nonzero scalar: the output is a gcd (`IsGcdOf`) in `ℚ[x]`. "With probability
`1 − 2md^m/b`" is read as "at least", for every sampling set `S` of `b` integers of height at most
`h`. `x₁` is the variable `0 : Fin m`. -/
theorem lemma_2_13 :
    ∃ (Fam : List ℕ → ThresholdCircuit) (wOut : List ℕ → ℕ),
      IsUniformTC0 Fam ∧ PolyComputableIndexFn Fam (fun ι => [wOut ι]) ∧
      ∀ (m d h : ℕ) (hm : 0 < m),
        (Fam [m, d, h]).numIn = gcdInputLength m d h ∧
        (Fam [m, d, h]).numOut = (expList m d).length * (wOut [m, d, h] + 1) ∧
        ∀ fc gc : Fin (expList m d).length → ℤ, (∀ j, |fc j| ≤ 2 ^ h ∧ |gc j| ≤ 2 ^ h) →
          (⟨0, hm⟩ : Fin m) ∈ (MvPolynomial.homogeneousComponent (densePoly m d fc).totalDegree
              (densePoly m d fc)).vars →
          (⟨0, hm⟩ : Fin m) ∈ (MvPolynomial.homogeneousComponent (densePoly m d gc).totalDegree
              (densePoly m d gc)).vars →
          ∀ S : Finset ℤ, S.Nonempty → (∀ s ∈ S, |s| ≤ 2 ^ h) →
            (1 : ℝ) - 2 * (m : ℝ) * (d : ℝ) ^ m / (S.card : ℝ) ≤
              unifProb S (fun a : Fin (m - 1) → ℤ =>
                IsGcdOf (MvPolynomial.map (Int.castRingHom ℚ) (densePoly m d fc))
                  (MvPolynomial.map (Int.castRingHom ℚ) (densePoly m d gc))
                  (MvPolynomial.map (Int.castRingHom ℚ)
                    (gcdOutputPoly m d (wOut [m, d, h])
                      ((Fam [m, d, h]).output fun i => (gcdInput m d h fc gc a).getD i false)))) := by sorry

end ChowFormsCH
