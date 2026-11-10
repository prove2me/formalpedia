-- Prove2me | Theorems.Thm_EllipticRootFinding_Online_remark_5_4
-- name    : EllipticRootFinding.Online.remark_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:03:31.224207+00:00
-- url     : https://prove2.me/theorems/bc46e0a4-c1a4-4128-83fe-2b6852beba45
-- title:
--   Remark 5.4 — ψ_r at a generic point modulo u in Õ(log r · deg u) operations
-- statement:
--   Let $F$ be a finite field of characteristic greater than $3$ and $E : Y^2 = X^3 + aX + b$ an elliptic curve over $F$ ($4a^3 + 27b^2 \neq 0$). For $r \ge 1$ let $\psi_r(X, Y)$ be the $r$-th division polynomial in the normalization of p. 25: $\psi_r = \Psi_r(X)$ for odd $r$ and $\psi_r = 2Y\Psi_r(X)$ for even $r$. Given a monic $u \in F[X]$ and $\varphi_x, \varphi_y \in F[X]$ of degree less than $\deg u$, the task is to output
--   $$\psi_r(\varphi_x, \varphi_y) \bmod u.$$
--   The statement is: there are one program $P$ of the machine and constants $K, \kappa > 0$ such that, for every such field, curve, $r$, $u$, $\varphi_x$, $\varphi_y$, $P$ halts with this polynomial after at most $K\varphi\log(e+\varphi)^\kappa$ counted operations, where $\varphi = \log r \cdot \deg u$.
--
--   This is the evaluation used at Line 12 of Algorithm 4 to test membership in a torsion subgroup.
--
--   **Formalization Note.** $\psi_r$ is Mathlib's `WeierstrassCurve.Ψ r` of the short curve (not the unreduced `WeierstrassCurve.ψ r`), evaluated at $X := \varphi_x$, $Y := \varphi_y$; input layout $[q, a, b, r, u, \varphi_x, \varphi_y]$.
--
--   Differences from the source:
--   - encoding: arithmetic operations in Fq (model of computation not specified) → one finite program (List Instr) independent of the field, run over every finite field F of characteristic > 3; field +, −, ×, inverse (0⁻¹ = 0) and zero-test cost 1; the constants 0 and 1, copies of field registers and all integer instructions (unbounded integers) are free; no integer-to-field cast, no other field constant; input and output are Val values in a fixed self-delimiting register layout; reason: the paper counts only operations in Fq; the machine makes 'algorithm' and 'operation' precise without granting a non-uniform family or free field information
--   - reading: the value … can be computed within Õ(log r · deg(u)) operations → there exists a program of the machine computing ψ_r(φ_x, φ_y) mod u within the bound on every valid input; reason: the remark asserts the existence of such a computation
--   - reading: for a fixed elliptic curve E → the program and K, κ are uniform over all curves: a and b are inputs; reason: the stronger of the two readings, and the one Algorithm 4 (Proposition 5.5) needs, where E is an input
--   - generalization: u = u_i of Line 12 of Algorithm 4 (monic, split, separable) and (φ_x, φ_y) a generic point of E modulo u → u any monic polynomial; φ_x, φ_y any polynomials of degree < deg u (no curve equation modulo u is assumed); reason: the normalized ψ_r is linear in Y and its recurrences are polynomial identities in X, so the computation needs neither hypothesis; the Line 12 inputs satisfy these weaker conditions
--   - encoding: Õ(φ) of Section 3: there exist C, κ > 0 such that for all inputs the cost is ≤ C φ log(exp(1) + φ)^κ → ∃ K κ > 0 quantified before the field and every input; cost ≤ softOBound K κ φ = K·φ·Real.log(Real.exp 1 + φ)^κ, natural log of q = Fintype.card F; reason: verbatim Section 3 definition over the domain of all valid inputs; the constant is named K because C is Polynomial.C
--   - encoding: p a prime greater than 3, q = p^e, Fq (with an Fp-basis and multiplication table when given as input) → an arbitrary finite field F : Type with 3 < ringChar F and q = Fintype.card F; algorithmic items receive q as an integer and no Fp-basis; reason: same fields; the algebraic lemmas require no field presentation, and algorithmic items use the uniform field-operation model without a basis
--   - encoding: polynomials, integers and field elements as algorithm inputs and outputs → inputs: a polynomial g as its coefficients 0..natDegree g; outputs: a polynomial is read from any finite coefficient list (trailing zeros allowed, IsPolyVal); deg as natDegree in the cost (natDegree 0 = 0); reason: fixed documented layout shared by every item; the reading of an output is exact equality of polynomials
--   - encoding: ψ_r(X, Y) with ψ_r = Ψ_r(X) for odd r and 2YΨ_r(X) for even r → WeierstrassCurve.Ψ r of shortCurve a b (C (preΨ r) · (2Y if r even, 1 if r odd)), evaluated by eval₂ (compRingHom φ_x) φ_y and reduced by %ₘ u; reason: Mathlib's Ψ is exactly the paper's normalization
-- source:
--   Spaenlehauer, Deterministic Root-Finding over Finite Fields with Elliptic Curves, arXiv:2610.32508 (version held, sha256 c72ee273…), p. 25, Remark 5.4

import Mathlib
import Definitions.Def_EllipticRootFinding_Online_Machine
import Definitions.Def_EllipticRootFinding_Online_Complexity
import Definitions.Def_EllipticRootFinding_Online_Curves

open Polynomial

namespace EllipticRootFinding.Online

/-- Remark 5.4 (p. 25), read as: one program of the machine, on every finite field `F` of
characteristic `> 3` and every elliptic curve `E : Y² = X³ + aX + b` (uniformly in `E`), given
`r ≥ 1`, a monic `u` and `φ_x, φ_y` of degree `< deg u`, outputs `ψ_r(φ_x, φ_y) mod u` within
`K · φ · log(e + φ)^κ` counted field operations, `φ = log r · deg u`, `K, κ > 0` fixed before all
inputs.

`ψ_r` is the paper's normalization (p. 25): `Ψ_r(X)` for odd `r` and `2Y Ψ_r(X)` for even `r`,
i.e. Mathlib's `WeierstrassCurve.Ψ r` of the short curve; it is evaluated at `X := φ_x`,
`Y := φ_y` and reduced modulo `u`. Input layout `[q, a, b, r, u, φ_x, φ_y]`. -/
theorem remark_5_4 :
    ∃ P : Program, ∃ K κ : ℝ, 0 < K ∧ 0 < κ ∧
      ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F], 3 < ringChar F →
      ∀ (a b : F), 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 →
      ∀ (r : ℕ), 1 ≤ r →
      ∀ (u φx φy : F[X]), u.Monic → φx.degree < u.degree → φy.degree < u.degree →
        Computes P
          (Val.ofList [Val.int (Fintype.card F : ℤ), Val.fld a, Val.fld b, Val.int (r : ℤ),
            polyVal u, polyVal φx, polyVal φy])
          (fun out => IsPolyVal out
            ((((shortCurve a b).Ψ (r : ℤ)).eval₂ (Polynomial.compRingHom φx) φy) %ₘ u))
          (softOBound K κ (Real.log r * (u.natDegree : ℝ))) := by sorry

end EllipticRootFinding.Online
