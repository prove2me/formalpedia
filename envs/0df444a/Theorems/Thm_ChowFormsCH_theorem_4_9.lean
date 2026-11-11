-- Prove2me | Theorems.Thm_ChowFormsCH_theorem_4_9
-- name    : ChowFormsCH.theorem_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:00:05.108748+00:00
-- url     : https://prove2.me/theorems/5b8430e5-5961-4a66-89d4-92b6aa297f9a
-- title:
--   Theorem 4.9 — uniform constant-depth threshold circuits compute $\mathbb Z$-multiples of the Chow forms of all equidimensional components (corrected: $(d+2)^{\mathrm{poly}(n)}$)
-- statement:
--   There exist a polylogtime-uniform family of constant-depth threshold circuits $C^{\mathrm{CHOW}}$, indexed by $n,m,d_1,\dots,d_m,h$, with the following properties.
--
--   1. $C^{\mathrm{CHOW}}_{n,m,d_1,\dots,d_m,h}$ takes as input forms $F_1,\dots,F_m\in\mathbb Q[x_0,\dots,x_n]$ of degrees $d_1,\dots,d_m$ and height at most $h$ in the dense representation, and $r=5\cdot m\cdot(n+1)^3$ integers $a_1,\dots,a_r$ of height at most $h$.
--   2. Its output is a set of $n+1$ polynomials in the dense representation. If $a_1,\dots,a_r$ are independently and uniformly sampled from a set of $b$ integers of height at most $h$, then with probability at least
--   $$
--   1-\frac{100\,n^2\,(n d^{\,n})^{n^2}}{b},\qquad d=\max_i d_i,
--   $$
--   for every $k=0,\dots,n$ the $k$-th output is a nonzero integer multiple of the Chow form $C_{V_k}$ of the $k$-equidimensional component $V_k$ of $V(F_1,\dots,F_m)\subseteq\mathbb P^n(\overline{\mathbb Q})$.
--   3. The size of $C^{\mathrm{CHOW}}_{n,m,d_1,\dots,d_m,h}$ is $\mathrm{poly}\big(h,n,m,(d+2)^{\mathrm{poly}(n)}\big)$.
--
--   This is the paper's main technical result: simulating such circuits in the counting hierarchy gives the CH bounds for Chow forms, degrees and equidimensional-component membership (Theorems 1.1, 1.2, 1.4, 1.5).
--
--   **Formalization Note** Inputs and outputs follow the fixed layouts of `chowOutputPoly`; the output degree bound $N$ and width $w$ are chosen by the family and computable from the index within the uniformity time bound. "Constant depth" is one bound $\Delta$ for all indices, and the size bound is $c\,(h+n+m+2)^c\,(d+2)^{c(n+1)^c}$ for one constant $c$. Correctness is claimed for valid encodings (nonzero denominators).
--
--   Differences from the source:
--   - correction: size poly(h, n, m, (d + 1)^poly(n)) → size ≤ c·(h+n+m+2)^c·(d+2)^(c(n+1)^c); reason: false at d = 0: with m = 1, d₁ = 0, h = 0, F₁ = 0 gives V = P^n, whose n-dimensional component has Chow form det(u_{i,j}) with (n+1)! monomials, while F₁ = 1 gives V = ∅ and Chow form 1, so the (n+1)! corresponding output coefficients depend on the input and the circuit has at least (n+1)! wires, not poly(n); for d ≥ 1, d + 2 ≤ (d + 1)² makes both bounds the same class
--   - reading: the computed polynomials are ℤ-multiples of the Chow forms → nonzero integer multiples z·C_{V_k}, z ∈ ℤ∖{0}; reason: with the zero multiple the circuit outputting 0 would satisfy the theorem; the proof normalizes the output to leading coefficient 1
--   - reading: forms in ℚ[x] of height at most h (height defined for integers) → each coefficient a pair (p, q), q ≠ 0, |p|, |q| ≤ 2^h; correctness for valid encodings only; reason: §2.4 represents rationals as pairs of integers; this contains the integer-coefficient reading (q = 1)
--   - reading: inputs independently and uniformly sampled from a set of size b → for every finite set S of b ≥ 1 integers of height at most h, the fraction of a ∈ S^r with correct output is at least the bound; reason: the random integers are inputs of height at most h; the claim is for every such sampling set
--   - reading: polylogtime-uniform: time polynomial in log(s) + log(k) + Σ log(nᵢ) → time polynomial in the binary lengths of s, k and the nᵢ (each nᵢ counting at least one bit), for sequential machines; reason: with ⌊log₂⌋, an index (n, m, 1, …, 1, h) with many entries leaves a sequential machine too little time to read it
--   - encoding: threshold circuits, size, constant depth, dense input and output representations (not fully specified) → AND/OR/NOT/MAJORITY gates, size = number of wires, one depth bound Δ; fixed layouts with integers in sign and h + 1 magnitude bits, output degree bound and width chosen by the family and computable from the index; reason: the standard model; fixed encodings so that no decoder can do the work
--   - encoding: V(F₁, …, F_m) ⊆ P^n and its equidimensional components → the punctured-cone model of P^n over the algebraic closure of ℚ, components by topological Krull dimension, empty components with Chow form 1; reason: the paper works over ℚ̄; an empty V_k has Chow form 1 (proof of Theorem 4.9)
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Theorem 4.9, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_ChowFormsCH_comps
import Definitions.Def_ChowFormsCH_IsChowForm
import Definitions.Def_ChowFormsCH_IsSqfPart
import Definitions.Def_ChowFormsCH_PolylogtimeUniform
import Definitions.Def_ChowFormsCH_chowOutputPoly

set_option autoImplicit false

namespace ChowFormsCH

/-- **Theorem 4.9** (Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric computations in CH
via Chow forms*, arXiv:2611.05289, held version, sha256 75e796c6…, p.34), corrected: size
`poly(h, n, m, (d+2)^{poly(n)})`. There exists a polylogtime-uniform family of constant-depth threshold
circuits `C^CHOW` indexed by `n, m, d₁, …, d_m, h` such that:

* `C^CHOW_{n,m,d₁,…,d_m,h}` takes as input forms `F₁, …, F_m ∈ ℚ[x₀, …, xₙ]` of degrees `d₁, …, d_m` and
  height at most `h` in the dense representation, and `r = 5·m·(n+1)³` integers `a₁, …, a_r` of height
  at most `h`;
* its output is a set of `n + 1` polynomials in the dense representation; if `a₁, …, a_r` are
  independently and uniformly sampled from a set of size `b`, then with probability at least
  `1 − 100n²(nd^n)^{n²}/b` the computed polynomials are `ℤ`-multiples of the Chow forms of the
  equidimensional components `V₀, …, Vₙ` of `V(F₁, …, F_m)`, where `d = max_i d_i`;
* its size is `poly(h, n, m, (d+2)^{poly(n)})` (the source prints `(d+1)`, see below).

**Formalization Note** The family is indexed by lists `(n, m, d₁, …, d_m, h)` (`chowIndex`). Inputs
follow the fixed layout `chowInput` (rational coefficients as pairs `(p, q)`, `q ≠ 0`, `|p|, |q| ≤ 2^h`;
integers with a sign bit and `h + 1` magnitude bits); outputs follow the fixed layout
`chowOutputPoly`, with a degree bound `N` and bit width `w` chosen by the family and computable from
the index (`PolyComputableIndexFn`). Correctness is claimed for valid encodings. "`ℤ`-multiple" is
read as a nonzero multiple. The variety `V(F₁, …, F_m)` and its components live in `P^n` over the
algebraic closure of `ℚ`; `V_k` is `equidimComponent V k` (empty components have Chow form `1`). The
sampling statement holds for every set `S` of `b ≥ 1` integers of height at most `h`. "Constant depth"
is one bound `Δ` for all indices; "size `poly(h, n, m, (d+2)^{poly(n)})`" is
`size ≤ c·(h+n+m+2)^c·(d+2)^{c(n+1)^c}` for one `c`. Correction: for `d = 0` (e.g. `m = 1`, `F₁` a
constant) the source's bound `poly(h, n, m, 1)` is polynomial in `n`, but when `F₁ = 0` the output for
`k = n` must be a nonzero multiple of the Chow form of `P^n`, the determinant of `(u_{i,j})`, whose
`(n+1)!` monomials each need an output gate depending on the input; `(d+2)` replaces `(d+1)`, which
changes nothing for `d ≥ 1` (`d + 2 ≤ (d+1)²`). -/
theorem theorem_4_9 :
    ∃ (Fam : List ℕ → ThresholdCircuit) (Δ c : ℕ) (N w : List ℕ → ℕ),
      PolylogtimeUniform Fam ∧ PolyComputableIndexFn Fam (fun ι => [N ι, w ι]) ∧
      ∀ (n m : ℕ) (ds : Fin m → ℕ) (h : ℕ),
        (Fam (chowIndex n m ds h)).HasDepthAtMost Δ ∧
        (Fam (chowIndex n m ds h)).size ≤
          c * (h + n + m + 2) ^ c * (Finset.univ.sup ds + 2) ^ (c * (n + 1) ^ c) ∧
        (Fam (chowIndex n m ds h)).numIn = chowInputLength n m ds h ∧
        (Fam (chowIndex n m ds h)).numOut =
          chowOutputLength n (N (chowIndex n m ds h)) (w (chowIndex n m ds h)) ∧
        ∀ coef : (i : Fin m) → Fin (homExps (n + 1) (ds i)).length → ℤ × ℤ,
          (∀ i j, (coef i j).2 ≠ 0 ∧ |(coef i j).1| ≤ 2 ^ h ∧ |(coef i j).2| ≤ 2 ^ h) →
          ∀ S : Finset ℤ, S.Nonempty → (∀ s ∈ S, |s| ≤ 2 ^ h) →
            (1 : ℝ) - 100 * (n : ℝ) ^ 2 * ((n : ℝ) * ((Finset.univ.sup ds : ℕ) : ℝ) ^ n) ^ (n ^ 2)
                / (S.card : ℝ) ≤
              unifProb S (fun a : Fin (numRandom n m) → ℤ =>
                ∀ k : Fin (n + 1), ∃ z : ℤ, z ≠ 0 ∧
                  ∃ Cf : MvPolynomial (Fin ((k : ℕ) + 1) × Fin (n + 1)) (AlgebraicClosure ℚ),
                    IsNormalizedChowForm
                      (equidimComponent
                        (projZero (Set.range fun i : Fin m =>
                          MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ))
                            (formOfData n (ds i) (coef i)))) k) k Cf ∧
                    MvPolynomial.map (Int.castRingHom (AlgebraicClosure ℚ))
                        (chowOutputPoly n (N (chowIndex n m ds h)) (w (chowIndex n m ds h))
                          ((Fam (chowIndex n m ds h)).output
                            fun i => (chowInput n m ds h coef a).getD i false) k)
                      = z • Cf) := by sorry

end ChowFormsCH
