-- Prove2me | Theorems.Thm_EllipticRootFinding_Online_proposition_5_5
-- name    : EllipticRootFinding.Online.proposition_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:03:37.128434+00:00
-- url     : https://prove2.me/theorems/c1c3db9d-614f-4b15-96cc-0044eba6bcaa
-- title:
--   Proposition 5.5 — Algorithm 4 (one torsion level of the split) in Õ(ℓ² deg D log q), Õ(ℓ deg D log q) if the level quotient is cyclic
-- statement:
--   Let $F$ be a finite field with $q$ elements and characteristic greater than $3$, $E : Y^2 = X^3 + aX + b$ an elliptic curve over $F$, $N = |E(F)|$, $\ell$ a prime dividing $N$ and $N_\ell = N/\ell^{v_\ell(N)}$. Algorithm 4 (ECPrimaryFactoAtLevelm) receives a positive integer $m \le v_\ell(\exp E(F))$, a set $J$ of representatives of $E(F)[\ell^m]/E(F)[\ell^{m-1}]$, and a split divisor $D = \sum_i D_i$ of simple divisors in $(u,v)$-coordinates whose support lies in $E(F)[N_\ell \ell^m]$ and meets neither $J$ nor $-J$. It must output, for every $P \in J$, the split divisor
--   $$D(P) = \{R \in D : [R - P] \in E(F)[N_\ell\,\ell^{m-1}]\}.$$
--   The statement is: there are one program $P$ and constants $K, \kappa > 0$ such that, for every such field and input, $P$ halts with such an output after at most $K\varphi\log(e+\varphi)^\kappa$ counted operations with $\varphi = \ell^2 \deg D \log q$, and after at most the same expression with $\varphi = \ell \deg D \log q$ whenever $E(F)[\ell^m]/E(F)[\ell^{m-1}]$ is cyclic.
--
--   This is one level of the elliptic analogue of the Mignotte–Schnorr split, iterated by Algorithm 5.
--
--   **Formalization Note.** Input layout $[q, a, b, N, \ell, m, J, D]$, $J$ a list without repetition; output one representation per element of $J$, in the order of $J$. Cyclicity of the quotient is stated elementwise: some $G \in E[\ell^m]$ has every $R \in E[\ell^m]$ congruent to a multiple $kG$ modulo $E[\ell^{m-1}]$.
--
--   Differences from the source:
--   - encoding: arithmetic operations in Fq (model of computation not specified) → one finite program (List Instr) independent of the field, run over every finite field F of characteristic > 3; field +, −, ×, inverse (0⁻¹ = 0) and zero-test cost 1; the constants 0 and 1, copies of field registers and all integer instructions (unbounded integers) are free; no integer-to-field cast, no other field constant; input and output are Val values in a fixed self-delimiting register layout; reason: the paper counts only operations in Fq; the machine makes 'algorithm' and 'operation' precise without granting a non-uniform family or free field information
--   - reading: Algorithm 4 (ECPrimaryFactoAtLevelm) terminates and is correct and performs at most the stated number of operations → there exists a program of the machine that, on every input satisfying Algorithm 4's Input block, halts with an output satisfying its Output block within the stated bound; reason: the paper does not fix its subroutines (fast GCD, remainder trees, CRT, characteristic polynomials, modular composition), so the claim is read as existence of an implementation of the stated contract
--   - encoding: Õ(φ) of Section 3: there exist C, κ > 0 such that for all inputs the cost is ≤ C φ log(exp(1) + φ)^κ → ∃ K κ > 0 quantified before the field and every input; cost ≤ softOBound K κ φ = K·φ·Real.log(Real.exp 1 + φ)^κ, natural log of q = Fintype.card F; reason: verbatim Section 3 definition over the domain of all valid inputs; the constant is named K because C is Polynomial.C
--   - encoding: p a prime greater than 3, q = p^e, Fq (with an Fp-basis and multiplication table when given as input) → an arbitrary finite field F : Type with 3 < ringChar F and q = Fintype.card F; algorithmic items receive q as an integer and no Fp-basis; reason: same fields; the algebraic lemmas require no field presentation, and algorithmic items use the uniform field-operation model without a basis
--   - encoding: E an elliptic curve Y² = X³ + aX + b over Fq, E(Fq) with ∞ and the chord-and-tangent law → a, b ∈ F with 4a³ + 27b² ≠ 0; points are Mathlib's WeierstrassCurve.Affine.Point of shortCurve a b (abbreviation Pt a b) with its AddCommGroup; order is addOrderOf; E(Fq)[n] is IsTors n (n • P = 0); exponent(E(Fq)) is AddMonoid.exponent; reason: Mathlib's nonsingular points of a nonsingular short Weierstrass curve are exactly the paper's E(Fq)
--   - encoding: split divisor D (Definition 4.3) encoded by the (u, v)-coordinates of simple divisors with disjoint supports and a flag for ∞; deg(D) its number of points → support D : Finset (Pt a b); RepresentsSplit inf L D with SimpleUV (∞ excluded, distinct abscissae, u = ∏(X − x(P)), deg v < deg u, v(x(P)) = y(P)); deg D = D.card; output read by IsSplitVal; reason: a split divisor is a set of distinct points, so a Finset is faithful; the (u, v) conditions are those of Definition 4.3
--   - encoding: polynomials, integers and field elements as algorithm inputs and outputs → inputs: a polynomial g as its coefficients 0..natDegree g; outputs: a polynomial is read from any finite coefficient list (trailing zeros allowed, IsPolyVal); deg as natDegree in the cost (natDegree 0 = 0); reason: fixed documented layout shared by every item; the reading of an output is exact equality of polynomials
--   - reading: Nℓ = |E(Fq)|/ℓ^{valℓ(|E(Fq)|)} is used by the algorithm, while |E(Fq)| is not listed in its Input block → N = Nat.card (Pt a b) is part of the input (an integer); reason: the algorithm computes Nℓ from |E(Fq)|; the caller (Algorithm 6) has it from fac(N) (Remark 5.7), and the field size alone does not determine it
--   - encoding: a set J of representatives for the classes in E(Fq)[ℓ^m]/E(Fq)[ℓ^{m−1}]; the family (D(P))_{P∈J} → a list J without repetition, contained in E[ℓ^m], with exactly one element in each class modulo E[ℓ^{m−1}]; output a list of split-divisor representations aligned with J; reason: same set and family in a fixed order
--   - encoding: E(Fq)[ℓ^m]/E(Fq)[ℓ^{m−1}] is cyclic → ∃ G ∈ E[ℓ^m], ∀ R ∈ E[ℓ^m], ∃ k : ℤ, R − k•G ∈ E[ℓ^{m−1}]; reason: equivalent definition of cyclicity of the quotient group
--   - encoding: the general bound and its improvement in the cyclic case → one program, one pair K, κ, and two conjuncts: the general bound, and the improved bound under the cyclicity hypothesis; reason: both clauses of the proposition, about the same algorithm
-- source:
--   Spaenlehauer, Deterministic Root-Finding over Finite Fields with Elliptic Curves, arXiv:2610.32508 (version held, sha256 c72ee273…), p. 25, Proposition 5.5 (Algorithm 4, p. 24)

import Mathlib
import Definitions.Def_EllipticRootFinding_Online_Machine
import Definitions.Def_EllipticRootFinding_Online_Complexity
import Definitions.Def_EllipticRootFinding_Online_Curves

open Polynomial Classical

namespace EllipticRootFinding.Online

/-- Proposition 5.5 (p. 25) for Algorithm 4 (ECPrimaryFactoAtLevelm, p. 24), read as: one program
of the machine meets Algorithm 4's Input/Output contract on every finite field `F` of
characteristic `> 3`, within `K · φ · log(e + φ)^κ` counted field operations,
`φ = ℓ² · deg D · log q`, and within the same expression for `φ = ℓ · deg D · log q` whenever
`E(F)[ℓ^m]/E(F)[ℓ^{m−1}]` is cyclic; `K, κ > 0` fixed before all inputs.

Input layout `[q, a, b, N, ℓ, m, J, D]` with `N = |E(F)|` and `N_ℓ = N / ℓ^{val_ℓ N}`: `ℓ` a
prime dividing `N`; `1 ≤ m ≤ val_ℓ(exponent E(F))`; `J` (a list without repetition) a set of
representatives of `E(F)[ℓ^m]/E(F)[ℓ^{m−1}]`; `D` a list of `(u, v)`-coordinates of simple
divisors with disjoint supports, its support in `E(F)[N_ℓ · ℓ^m]` and disjoint from `J` and `−J`.
Output: one split divisor per `P ∈ J`, in the order of `J`, namely
`D(P) = {R ∈ D : [R − P] ∈ E(F)[N_ℓ · ℓ^{m−1}]}`. -/
theorem proposition_5_5 :
    ∃ P : Program, ∃ K κ : ℝ, 0 < K ∧ 0 < κ ∧
      ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F], 3 < ringChar F →
      ∀ (a b : F), 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 →
      ∀ (N : ℕ), N = Nat.card (Pt a b) →
      ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∣ N →
      ∀ (m : ℕ), 1 ≤ m → m ≤ padicValNat ℓ (AddMonoid.exponent (Pt a b)) →
      ∀ (J : List (Pt a b)), J.Nodup → (∀ R ∈ J, IsTors (ℓ ^ m) R) →
        (∀ R : Pt a b, IsTors (ℓ ^ m) R → ∃! S, S ∈ J ∧ IsTors (ℓ ^ (m - 1)) (R - S)) →
      ∀ (D : Finset (Pt a b)) (L : List (F[X] × F[X])), RepresentsSplit false L D →
        (∀ R ∈ D, IsTors (N / ℓ ^ padicValNat ℓ N * ℓ ^ m) R) →
        (∀ R ∈ D, R ∉ J ∧ -R ∉ J) →
        let input : Val F := Val.ofList [Val.int (Fintype.card F : ℤ), Val.fld a, Val.fld b,
          Val.int (N : ℤ), Val.int (ℓ : ℤ), Val.int (m : ℤ), Val.ofList (J.map pointVal),
          splitVal false L]
        let spec : Val F → Prop := fun out => ∃ ws : List (Val F), out = Val.ofList ws ∧
          List.Forall₂ (fun w S => IsSplitVal w
            (D.filter fun R => IsTors (N / ℓ ^ padicValNat ℓ N * ℓ ^ (m - 1)) (R - S))) ws J
        Computes P input spec
            (softOBound K κ ((ℓ : ℝ) ^ 2 * (D.card : ℝ) * Real.log (Fintype.card F))) ∧
          ((∃ G : Pt a b, IsTors (ℓ ^ m) G ∧
              ∀ R : Pt a b, IsTors (ℓ ^ m) R → ∃ k : ℤ, IsTors (ℓ ^ (m - 1)) (R - k • G)) →
            Computes P input spec
              (softOBound K κ ((ℓ : ℝ) * (D.card : ℝ) * Real.log (Fintype.card F)))) := by sorry

end EllipticRootFinding.Online
