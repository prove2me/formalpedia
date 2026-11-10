-- Prove2me | Theorems.Thm_EllipticRootFinding_Online_theorem_1_3
-- name    : EllipticRootFinding.Online.theorem_1_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:03:46.529062+00:00
-- url     : https://prove2.me/theorems/30d54f6c-7013-47fc-8a72-4d8ebfa44ad5
-- title:
--   Theorem 1.3 — deterministic root-finding in Õ(Ξ(D)² n log² q + n^ω log q + n log³ q) operations in F_q
-- statement:
--   Let $F$ be a finite field with $q$ elements and characteristic $p > 3$. Let $f \in F[X]$ be split (a product of linear factors) and separable, of degree $n \ge 0$, not necessarily monic, and let $D$ be a valid elliptic preprocessing datum for $F$, with $\Xi(D)$ the largest prime dividing $|E(F)| \cdot |\tilde E(F)|$.
--
--   For every feasible exponent $\omega \in [2, 3]$ of matrix multiplication there are one program $P$ of the uniform machine and constants $K, \kappa > 0$ such that, for every such $F$, $f$ and $D$, the program on input $(q, f, D)$ halts and outputs a list without repetition of exactly the roots of $f$ in $F$, after at most $K\varphi\log(e+\varphi)^\kappa$ counted operations in $F$, where
--   $$\varphi = \Xi(D)^2\, n \log^2 q + n^{\omega} \log q + n \log^3 q.$$
--   The cost of constructing and verifying $D$ is excluded: validity of $D$ is a hypothesis.
--
--   This is the paper's main result: deterministic, unconditional root-finding whose cost depends on the field only through $\log q$ and $\Xi(D)$, independently of the factorization of $q - 1$.
--
--   **Formalization Note.** The input layout is `onlineInput`; the output is a `fieldListVal`. At $n = 0$ the bound is $0$, so the program must answer the empty list without counted operations (see the paper's Theorem 5.8, p. 29, for Algorithm 6).
--
--   Differences from the source:
--   - encoding: arithmetic operations in Fq (model of computation not specified) → one finite program (List Instr) independent of the field, run over every finite field F of characteristic > 3; field +, −, ×, inverse (0⁻¹ = 0) and zero-test cost 1; the constants 0 and 1, copies of field registers and all integer instructions (unbounded integers) are free; no integer-to-field cast, no other field constant; input and output are Val values in a fixed self-delimiting register layout; reason: the paper counts only operations in Fq; the machine makes 'algorithm' and 'operation' precise without granting a non-uniform family or free field information
--   - reading: There is a deterministic algorithm (Algorithm 6) which … outputs all roots of f in Fq … performs at most Õ(…) arithmetic operations → ∃ a program of the machine which, on every valid input, halts with the roots within the bound; reason: the claim is the existence of an algorithm; Algorithm 6 is the paper's witness
--   - reading: ω ∈ [2, 3] a feasible exponent of matrix multiplication → ∀ ω, 2 ≤ ω → ω ≤ 3 → FeasibleMatMul ω → …, where FeasibleMatMul ω says one program of the same machine multiplies n × n matrices over every finite field of characteristic > 3 within C·n^ω operations for every n; K, κ may depend on ω; reason: the algorithm must run its linear algebra inside the same uniform model; no characteristic-polynomial or linear-system oracle is assumed
--   - encoding: Õ(φ) of Section 3: there exist C, κ > 0 such that for all inputs the cost is ≤ C φ log(exp(1) + φ)^κ → ∃ K κ > 0 quantified before the field and every input; cost ≤ softOBound K κ φ = K·φ·Real.log(Real.exp 1 + φ)^κ, natural log of q = Fintype.card F; reason: verbatim Section 3 definition over the domain of all valid inputs; the constant is named K because C is Polynomial.C
--   - encoding: p a prime greater than 3, q = p^e, Fq (with an Fp-basis and multiplication table when given as input) → an arbitrary finite field F : Type with 3 < ringChar F and q = Fintype.card F; algorithmic items receive q as an integer and no Fp-basis; reason: same fields; the algebraic lemmas require no field presentation, and algorithmic items use the uniform field-operation model without a basis
--   - encoding: outputs all roots of f in Fq ('Output: The set of roots of f', Algorithm 6) → the output is a list L of field elements without repetition such that x ∈ L ↔ f.IsRoot x for every x ∈ F; reason: a finite set given as a duplicate-free list
--   - encoding: split separable f ∈ Fq[X]; deg(f) → f.Splits and f.Separable (so f ≠ 0), any leading coefficient, n = f.natDegree, including n = 0; reason: Mathlib's notions; separability is coprimality with the derivative
--   - encoding: elliptic preprocessing datum D (Definition 1.2) for Fq, Ẽ the quadratic twist w.r.t. β, bases E(Fq) = ⟨G1⟩ ⊕ ⟨G2⟩ → Datum F with Datum.Valid: β nonsquare, 4a³ + 27b² ≠ 0, Ẽ : Y² = X³ + aβ⁻²X + bβ⁻³, N and Ñ the Nat.card of the point groups, fac lists the prime factorizations, bases as internal direct sums (generate and meet trivially); Ξ(D) from N·Ñ; reason: the twist model is the one of §3 and Algorithm 6; validity is a hypothesis, as 'excluding the cost of constructing and verifying D' says
-- source:
--   Spaenlehauer, Deterministic Root-Finding over Finite Fields with Elliptic Curves, arXiv:2610.32508 (version held, sha256 c72ee273…), p. 2, Theorem 1.3 (= Theorem 5.8, p. 29, for Algorithm 6)

import Mathlib
import Definitions.Def_EllipticRootFinding_Online_Machine
import Definitions.Def_EllipticRootFinding_Online_Complexity
import Definitions.Def_EllipticRootFinding_Online_Curves

open Polynomial

namespace EllipticRootFinding.Online

/-- Theorem 1.3 (p. 2): for every feasible exponent `ω ∈ [2, 3]` of matrix multiplication there
is one program of the machine (uniform over all finite fields) which, on every finite field `F`
with `q` elements and characteristic `> 3`, every split separable `f ∈ F[X]` (any leading
coefficient, any degree `n ≥ 0`) and every valid elliptic preprocessing datum `D`, halts and
outputs a list without repetition of exactly the roots of `f` in `F`, within
`K · φ · log(e + φ)^κ` counted field operations,
`φ = Ξ(D)² · n · log² q + n^ω · log q + n · log³ q`, with `K, κ > 0` fixed before `F`, `f`, `D`.
Input layout: `onlineInput`. -/
theorem theorem_1_3 :
    ∀ ω : ℝ, 2 ≤ ω → ω ≤ 3 → FeasibleMatMul ω →
    ∃ P : Program, ∃ K κ : ℝ, 0 < K ∧ 0 < κ ∧
      ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F], 3 < ringChar F →
      ∀ (f : F[X]), f.Splits → f.Separable →
      ∀ (D : Datum F), D.Valid →
        Computes P (onlineInput (Fintype.card F) f D)
          (fun out => ∃ L : List F, out = fieldListVal L ∧ L.Nodup ∧ ∀ x : F, x ∈ L ↔ f.IsRoot x)
          (softOBound K κ
            ((D.Xi : ℝ) ^ 2 * (f.natDegree : ℝ) * Real.log (Fintype.card F) ^ 2 +
              (f.natDegree : ℝ) ^ ω * Real.log (Fintype.card F) +
              (f.natDegree : ℝ) * Real.log (Fintype.card F) ^ 3)) := by sorry

end EllipticRootFinding.Online
