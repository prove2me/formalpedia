-- Prove2me | Theorems.Thm_EllipticRootFinding_Online_proposition_5_6
-- name    : EllipticRootFinding.Online.proposition_5_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:03:36.021098+00:00
-- url     : https://prove2.me/theorems/fbef3d7a-23d4-40f1-8cbf-fd590937b42c
-- title:
--   Proposition 5.6 — Algorithm 5 (decomposition along the ℓ-Sylow subgroup) in Õ(m(ℓ² deg D log q + deg D log² q + deg D^ω)), ℓ for ℓ² if E[ℓ^m] is cyclic
-- statement:
--   Let $F$ be a finite field with $q$ elements and characteristic greater than $3$, $E : Y^2 = X^3 + aX + b$ an elliptic curve over $F$, $N = |E(F)|$, $\ell$ a prime dividing $N$ and $N_\ell = N/\ell^{v_\ell(N)}$. Algorithm 5 (ECPrimaryFacto) receives an integer $0 \le m \le v_\ell(\exp E(F))$, generators $G_1, G_2$ of the $\ell$-Sylow subgroup $E(F)[\ell^\infty]$ with $\mathrm{order}(G_1)\,\mathrm{order}(G_2) = \ell^{v_\ell(N)}$, a split divisor $D$ with support in $E(F)[N_\ell \ell^m]$, and a nonsquare $\beta$. It must output a finite set $S \subset E(F)[\ell^m]$ and split divisors $D(Q)$, $Q \in S$, with
--   $$D(Q) = \{R \in D : [R - Q] \in E(F)[N_\ell]\}, \qquad \sum_{Q \in S} D(Q) = D.$$
--   The statement is: for every feasible exponent $\omega \in [2,3]$ there are one program $P$ and constants $K, \kappa > 0$ such that, for every such field and input, $P$ halts with such an output after at most $K\varphi\log(e+\varphi)^\kappa$ counted operations with $\varphi = m(\ell^2 \deg D \log q + \deg D \log^2 q + (\deg D)^\omega)$, and after at most the same expression with $\ell$ in place of $\ell^2$ whenever $E(F)[\ell^m]$ is cyclic.
--
--   Algorithm 6 calls this once per prime $\ell \mid N$ (and per prime of $\tilde N$ on the twist) to separate the lifted roots.
--
--   **Formalization Note.** Input layout $[q, a, b, N, \ell, m, G_1, G_2, D, \beta]$; output a list of pairs $[Q, D(Q)]$ with pairwise distinct $Q$; the sum is the sum of multisets.
--
--   Differences from the source:
--   - encoding: arithmetic operations in Fq (model of computation not specified) → one finite program (List Instr) independent of the field, run over every finite field F of characteristic > 3; field +, −, ×, inverse (0⁻¹ = 0) and zero-test cost 1; the constants 0 and 1, copies of field registers and all integer instructions (unbounded integers) are free; no integer-to-field cast, no other field constant; input and output are Val values in a fixed self-delimiting register layout; reason: the paper counts only operations in Fq; the machine makes 'algorithm' and 'operation' precise without granting a non-uniform family or free field information
--   - reading: Algorithm 5 (ECPrimaryFacto) terminates and is correct and performs at most the stated number of operations → there exists a program of the machine that, on every input satisfying Algorithm 5's Input block, halts with an output satisfying its Output block within the stated bound; reason: the paper does not fix its subroutines (fast GCD, remainder trees, CRT, characteristic polynomials, modular composition), so the claim is read as existence of an implementation of the stated contract
--   - reading: ω ∈ [2, 3] a feasible exponent of matrix multiplication → ∀ ω, 2 ≤ ω → ω ≤ 3 → FeasibleMatMul ω → …, where FeasibleMatMul ω says one program of the same machine multiplies n × n matrices over every finite field of characteristic > 3 within C·n^ω operations for every n; K, κ may depend on ω; reason: the algorithm must run its linear algebra inside the same uniform model; no characteristic-polynomial or linear-system oracle is assumed
--   - encoding: Õ(φ) of Section 3: there exist C, κ > 0 such that for all inputs the cost is ≤ C φ log(exp(1) + φ)^κ → ∃ K κ > 0 quantified before the field and every input; cost ≤ softOBound K κ φ = K·φ·Real.log(Real.exp 1 + φ)^κ, natural log of q = Fintype.card F; reason: verbatim Section 3 definition over the domain of all valid inputs; the constant is named K because C is Polynomial.C
--   - encoding: p a prime greater than 3, q = p^e, Fq (with an Fp-basis and multiplication table when given as input) → an arbitrary finite field F : Type with 3 < ringChar F and q = Fintype.card F; algorithmic items receive q as an integer and no Fp-basis; reason: same fields; the algebraic lemmas require no field presentation, and algorithmic items use the uniform field-operation model without a basis
--   - encoding: E an elliptic curve Y² = X³ + aX + b over Fq, E(Fq) with ∞ and the chord-and-tangent law → a, b ∈ F with 4a³ + 27b² ≠ 0; points are Mathlib's WeierstrassCurve.Affine.Point of shortCurve a b (abbreviation Pt a b) with its AddCommGroup; order is addOrderOf; E(Fq)[n] is IsTors n (n • P = 0); exponent(E(Fq)) is AddMonoid.exponent; reason: Mathlib's nonsingular points of a nonsingular short Weierstrass curve are exactly the paper's E(Fq)
--   - encoding: split divisor D (Definition 4.3) encoded by the (u, v)-coordinates of simple divisors with disjoint supports and a flag for ∞; deg(D) its number of points → support D : Finset (Pt a b); RepresentsSplit inf L D with SimpleUV (∞ excluded, distinct abscissae, u = ∏(X − x(P)), deg v < deg u, v(x(P)) = y(P)); deg D = D.card; output read by IsSplitVal; reason: a split divisor is a set of distinct points, so a Finset is faithful; the (u, v) conditions are those of Definition 4.3
--   - encoding: polynomials, integers and field elements as algorithm inputs and outputs → inputs: a polynomial g as its coefficients 0..natDegree g; outputs: a polynomial is read from any finite coefficient list (trailing zeros allowed, IsPolyVal); deg as natDegree in the cost (natDegree 0 = 0); reason: fixed documented layout shared by every item; the reading of an output is exact equality of polynomials
--   - reading: Nℓ = |E(Fq)|/ℓ^{valℓ(|E(Fq)|)} is used by the algorithm, while |E(Fq)| is not listed in its Input block → N = Nat.card (Pt a b) is part of the input (an integer); reason: the algorithm computes Nℓ from |E(Fq)|; the caller (Algorithm 6) has it from fac(N) (Remark 5.7), and the field size alone does not determine it
--   - encoding: generators G1, G2 of E(Fq)[ℓ^∞] (the points whose order is a power of ℓ) → AddSubgroup.closure {G₁, G₂} = {R | ∃ k, addOrderOf R = ℓ^k} as sets; reason: same condition
--   - encoding: a finite set S and tuples {(Q, D(Q))}_{Q∈S} with Σ_{Q∈S} D(Q) = D → a list of pairs [Q, D(Q)] with pairwise distinct Q; the sum of the multisets D(Q).val equals D.val; reason: formal sums of distinct points are multisets
--   - encoding: E(Fq)[ℓ^m] is cyclic → ∃ G ∈ E[ℓ^m], ∀ R ∈ E[ℓ^m], ∃ k : ℤ, R = k•G; reason: definition of a cyclic group
--   - encoding: the general bound and its improvement in the cyclic case → one program, one pair K, κ, and two conjuncts: the general bound, and the improved bound under the cyclicity hypothesis; reason: both clauses of the proposition, about the same algorithm
-- source:
--   Spaenlehauer, Deterministic Root-Finding over Finite Fields with Elliptic Curves, arXiv:2610.32508 (version held, sha256 c72ee273…), p. 26, Proposition 5.6 (Algorithm 5, p. 27)

import Mathlib
import Definitions.Def_EllipticRootFinding_Online_Machine
import Definitions.Def_EllipticRootFinding_Online_Complexity
import Definitions.Def_EllipticRootFinding_Online_Curves

open Polynomial Classical

namespace EllipticRootFinding.Online

/-- Proposition 5.6 (p. 26) for Algorithm 5 (ECPrimaryFacto, p. 27), read as: for every feasible
exponent `ω ∈ [2, 3]` of matrix multiplication, one program of the machine meets Algorithm 5's
Input/Output contract on every finite field `F` of characteristic `> 3`, within
`K · φ · log(e + φ)^κ` counted field operations,
`φ = m (ℓ² · deg D · log q + deg D · log² q + deg D^ω)`, and within the same expression with `ℓ`
in place of `ℓ²` whenever `E(F)[ℓ^m]` is cyclic; `K, κ > 0` fixed before all inputs.

Input layout `[q, a, b, N, ℓ, m, G₁, G₂, D, β]` with `N = |E(F)|` and `N_ℓ = N / ℓ^{val_ℓ N}`:
`ℓ` a prime dividing `N`; `0 ≤ m ≤ val_ℓ(exponent E(F))`; `G₁, G₂` generate the `ℓ`-Sylow
subgroup `E(F)[ℓ^∞]` (the points whose order is a power of `ℓ`) with
`order(G₁) · order(G₂) = ℓ^{val_ℓ N}`; `D` a split divisor (flag for `∞` and `(u, v)`-coordinates
of simple divisors with disjoint supports) with support in `E(F)[N_ℓ · ℓ^m]`; `β` a nonsquare.
Output: a list of pairs `[Q, D(Q)]`, the `Q` pairwise distinct (the set `S ⊂ E(F)[ℓ^m]`), with
`D(Q) = {R ∈ D : [R − Q] ∈ E(F)[N_ℓ]}` and `∑_{Q ∈ S} D(Q) = D` as formal sums. -/
theorem proposition_5_6 :
    ∀ ω : ℝ, 2 ≤ ω → ω ≤ 3 → FeasibleMatMul ω →
    ∃ P : Program, ∃ K κ : ℝ, 0 < K ∧ 0 < κ ∧
      ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F], 3 < ringChar F →
      ∀ (a b : F), 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 →
      ∀ (N : ℕ), N = Nat.card (Pt a b) →
      ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∣ N →
      ∀ (m : ℕ), m ≤ padicValNat ℓ (AddMonoid.exponent (Pt a b)) →
      ∀ (G₁ G₂ : Pt a b),
        (AddSubgroup.closure {G₁, G₂} : Set (Pt a b)) = {R | ∃ k : ℕ, addOrderOf R = ℓ ^ k} →
        addOrderOf G₁ * addOrderOf G₂ = ℓ ^ padicValNat ℓ N →
      ∀ (D : Finset (Pt a b)) (inf : Bool) (L : List (F[X] × F[X])), RepresentsSplit inf L D →
        (∀ R ∈ D, IsTors (N / ℓ ^ padicValNat ℓ N * ℓ ^ m) R) →
      ∀ (β : F), ¬ IsSquare β →
        let input : Val F := Val.ofList [Val.int (Fintype.card F : ℤ), Val.fld a, Val.fld b,
          Val.int (N : ℤ), Val.int (ℓ : ℤ), Val.int (m : ℤ), pointVal G₁, pointVal G₂,
          splitVal inf L, Val.fld β]
        let spec : Val F → Prop := fun out =>
          ∃ (ps : List (Pt a b × Finset (Pt a b))) (ws : List (Val F)),
            out = Val.ofList ws ∧
            List.Forall₂ (fun w QD => ∃ dv : Val F, w = Val.ofList [pointVal QD.1, dv] ∧
              IsSplitVal dv QD.2) ws ps ∧
            (ps.map Prod.fst).Nodup ∧
            (∀ QD ∈ ps, IsTors (ℓ ^ m) QD.1 ∧
              QD.2 = D.filter fun R => IsTors (N / ℓ ^ padicValNat ℓ N) (R - QD.1)) ∧
            (ps.map fun QD => QD.2.val).sum = D.val
        let d : ℝ := D.card
        let lq : ℝ := Real.log (Fintype.card F)
        Computes P input spec
            (softOBound K κ ((m : ℝ) * ((ℓ : ℝ) ^ 2 * d * lq + d * lq ^ 2 + d ^ ω))) ∧
          ((∃ G : Pt a b, IsTors (ℓ ^ m) G ∧
              ∀ R : Pt a b, IsTors (ℓ ^ m) R → ∃ k : ℤ, R = k • G) →
            Computes P input spec
              (softOBound K κ ((m : ℝ) * ((ℓ : ℝ) * d * lq + d * lq ^ 2 + d ^ ω)))) := by sorry

end EllipticRootFinding.Online
