-- Prove2me | Theorems.Thm_EllipticRootFinding_Online_proposition_5_3
-- name    : EllipticRootFinding.Online.proposition_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:03:48.1262+00:00
-- url     : https://prove2.me/theorems/d294df1f-dfbd-40b5-b04a-66776100d63a
-- title:
--   Proposition 5.3 — Algorithm 3 (translating a split divisor by a point) in Õ(deg D log² q + deg D^ω) operations
-- statement:
--   Let $F$ be a finite field with $q$ elements and characteristic greater than $3$, and $E : Y^2 = X^3 + aX + b$ an elliptic curve over $F$. Algorithm 3 (ECTranslation) receives a split divisor $D$ given as a sum of simple divisors with disjoint supports in $(u, v)$-coordinates, a point $Q \in E(F)$ such that neither $Q$ nor $-Q$ lies in the support of $D$, and a nonsquare $\beta$. It must output a representation of the split divisor
--   $$\sum_{P \in D} [P + Q].$$
--   The statement is: for every feasible exponent $\omega \in [2,3]$ of matrix multiplication there are one program $P$ of the machine and constants $K, \kappa > 0$ such that, for every such field and input, $P$ halts with such an output after at most $K\varphi\log(e+\varphi)^\kappa$ counted operations, where $\varphi = \deg D \cdot \log^2 q + (\deg D)^\omega$ and $\deg D$ is the number of points of $D$.
--
--   Translation by a rational point plays the role, on $E$, of the substitution $f(X) \mapsto f(\gamma X)$ in the cyclotomic Mignotte–Schnorr method; Algorithm 5 uses it to move a divisor between cosets.
--
--   **Formalization Note.** Input layout $[q, a, b, D, Q, \beta]$ with the $\infty$ flag of $D$ unset.
--
--   Differences from the source:
--   - encoding: arithmetic operations in Fq (model of computation not specified) → one finite program (List Instr) independent of the field, run over every finite field F of characteristic > 3; field +, −, ×, inverse (0⁻¹ = 0) and zero-test cost 1; the constants 0 and 1, copies of field registers and all integer instructions (unbounded integers) are free; no integer-to-field cast, no other field constant; input and output are Val values in a fixed self-delimiting register layout; reason: the paper counts only operations in Fq; the machine makes 'algorithm' and 'operation' precise without granting a non-uniform family or free field information
--   - reading: Algorithm 3 (ECTranslation) terminates and is correct and performs at most the stated number of operations → there exists a program of the machine that, on every input satisfying Algorithm 3's Input block, halts with an output satisfying its Output block within the stated bound; reason: the paper does not fix its subroutines (fast GCD, remainder trees, CRT, characteristic polynomials, modular composition), so the claim is read as existence of an implementation of the stated contract
--   - reading: ω ∈ [2, 3] a feasible exponent of matrix multiplication → ∀ ω, 2 ≤ ω → ω ≤ 3 → FeasibleMatMul ω → …, where FeasibleMatMul ω says one program of the same machine multiplies n × n matrices over every finite field of characteristic > 3 within C·n^ω operations for every n; K, κ may depend on ω; reason: the algorithm must run its linear algebra inside the same uniform model; no characteristic-polynomial or linear-system oracle is assumed
--   - encoding: Õ(φ) of Section 3: there exist C, κ > 0 such that for all inputs the cost is ≤ C φ log(exp(1) + φ)^κ → ∃ K κ > 0 quantified before the field and every input; cost ≤ softOBound K κ φ = K·φ·Real.log(Real.exp 1 + φ)^κ, natural log of q = Fintype.card F; reason: verbatim Section 3 definition over the domain of all valid inputs; the constant is named K because C is Polynomial.C
--   - encoding: p a prime greater than 3, q = p^e, Fq (with an Fp-basis and multiplication table when given as input) → an arbitrary finite field F : Type with 3 < ringChar F and q = Fintype.card F; algorithmic items receive q as an integer and no Fp-basis; reason: same fields; the algebraic lemmas require no field presentation, and algorithmic items use the uniform field-operation model without a basis
--   - encoding: E an elliptic curve Y² = X³ + aX + b over Fq, E(Fq) with ∞ and the chord-and-tangent law → a, b ∈ F with 4a³ + 27b² ≠ 0; points are Mathlib's WeierstrassCurve.Affine.Point of shortCurve a b (abbreviation Pt a b) with its AddCommGroup; order is addOrderOf; E(Fq)[n] is IsTors n (n • P = 0); exponent(E(Fq)) is AddMonoid.exponent; reason: Mathlib's nonsingular points of a nonsingular short Weierstrass curve are exactly the paper's E(Fq)
--   - encoding: split divisor D (Definition 4.3) encoded by the (u, v)-coordinates of simple divisors with disjoint supports and a flag for ∞; deg(D) its number of points → support D : Finset (Pt a b); RepresentsSplit inf L D with SimpleUV (∞ excluded, distinct abscissae, u = ∏(X − x(P)), deg v < deg u, v(x(P)) = y(P)); deg D = D.card; output read by IsSplitVal; reason: a split divisor is a set of distinct points, so a Finset is faithful; the (u, v) conditions are those of Definition 4.3
--   - encoding: polynomials, integers and field elements as algorithm inputs and outputs → inputs: a polynomial g as its coefficients 0..natDegree g; outputs: a polynomial is read from any finite coefficient list (trailing zeros allowed, IsPolyVal); deg as natDegree in the cost (natDegree 0 = 0); reason: fixed documented layout shared by every item; the reading of an output is exact equality of polynomials
--   - encoding: q, used by the call FiniteFieldEmbedding(q, …) at Line 12, not listed among the inputs → q = Fintype.card F is the first input; reason: the field is an input of every algorithm (§3); q is how the machine learns its size
-- source:
--   Spaenlehauer, Deterministic Root-Finding over Finite Fields with Elliptic Curves, arXiv:2610.32508 (version held, sha256 c72ee273…), p. 20, Proposition 5.3 (Algorithm 3, p. 21)

import Mathlib
import Definitions.Def_EllipticRootFinding_Online_Machine
import Definitions.Def_EllipticRootFinding_Online_Complexity
import Definitions.Def_EllipticRootFinding_Online_Curves

open Polynomial Classical

namespace EllipticRootFinding.Online

/-- Proposition 5.3 (p. 20) for Algorithm 3 (ECTranslation, p. 21), read as: for every feasible
exponent `ω ∈ [2, 3]` of matrix multiplication, one program of the machine meets Algorithm 3's
Input/Output contract on every finite field `F` of characteristic `> 3`, within
`K · φ · log(e + φ)^κ` counted field operations, `φ = deg D · log² q + deg D^ω`, with
`K, κ > 0` fixed before all inputs.

Input layout `[q, a, b, D, Q, β]`: the curve `E : Y² = X³ + aX + b`, the split divisor `D` (support
`D`, `deg D = |D|`) as a list of `(u, v)`-coordinates of simple divisors with disjoint supports
(no `∞` flag set), the point `Q` with `Q, −Q ∉ D`, and a nonsquare `β`. Output: a representation of
the split divisor `∑_{P ∈ D} [P + Q]`. -/
theorem proposition_5_3 :
    ∀ ω : ℝ, 2 ≤ ω → ω ≤ 3 → FeasibleMatMul ω →
    ∃ P : Program, ∃ K κ : ℝ, 0 < K ∧ 0 < κ ∧
      ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F], 3 < ringChar F →
      ∀ (a b : F), 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 →
      ∀ (D : Finset (Pt a b)) (L : List (F[X] × F[X])), RepresentsSplit false L D →
      ∀ (Q : Pt a b), Q ∉ D → -Q ∉ D →
      ∀ (β : F), ¬ IsSquare β →
        Computes P
          (Val.ofList [Val.int (Fintype.card F : ℤ), Val.fld a, Val.fld b, splitVal false L,
            pointVal Q, Val.fld β])
          (fun out => IsSplitVal out (D.image (· + Q)))
          (softOBound K κ ((D.card : ℝ) * Real.log (Fintype.card F) ^ 2 + (D.card : ℝ) ^ ω)) := by sorry

end EllipticRootFinding.Online
