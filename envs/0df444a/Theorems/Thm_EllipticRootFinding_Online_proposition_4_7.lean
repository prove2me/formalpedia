-- Prove2me | Theorems.Thm_EllipticRootFinding_Online_proposition_4_7
-- name    : EllipticRootFinding.Online.proposition_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:03:39.119202+00:00
-- url     : https://prove2.me/theorems/aa949bc1-6d03-45f0-9e53-f8e95bd4ab60
-- title:
--   Proposition 4.7 — Algorithm 2 (lifting a split polynomial to split divisors) in Õ(log q (deg f log q + deg h)) operations
-- statement:
--   Let $F$ be a finite field with $q$ elements and characteristic greater than $3$. Algorithm 2 (FiniteFieldEmbedding) receives $h \in F[X]$, a monic split separable $f \in F[X]$ coprime with $h$, and a nonsquare $\beta \in F^\times$. It must output $u_0, u_1, v_0, v_1 \in F[X]$ with $u_0, u_1$ monic, $u_0 u_1 = f$, $\deg v_0 < \deg u_0$, $\deg v_1 < \deg u_1$ and
--   $$v_0^2 \equiv h \pmod{u_0}, \qquad \beta v_1^2 \equiv h \pmod{u_1}.$$
--   The statement is: there are one program $P$ of the machine and constants $K, \kappa > 0$ such that, for every such field and input, $P$ halts with such an output after at most $K\varphi\log(e+\varphi)^\kappa$ counted operations, where $\varphi = \log q\,(\deg f \cdot \log q + \deg h)$.
--
--   This lifts the roots of $f$ to split divisors on $E$ and on its quadratic twist; it is Line 2 of Algorithm 6 and a subroutine of Algorithm 3.
--
--   **Formalization Note.** Input layout $[q, h, f, \beta]$; output $[u_0, u_1, v_0, v_1]$.
--
--   Differences from the source:
--   - encoding: arithmetic operations in Fq (model of computation not specified) → one finite program (List Instr) independent of the field, run over every finite field F of characteristic > 3; field +, −, ×, inverse (0⁻¹ = 0) and zero-test cost 1; the constants 0 and 1, copies of field registers and all integer instructions (unbounded integers) are free; no integer-to-field cast, no other field constant; input and output are Val values in a fixed self-delimiting register layout; reason: the paper counts only operations in Fq; the machine makes 'algorithm' and 'operation' precise without granting a non-uniform family or free field information
--   - reading: Algorithm 2 (FiniteFieldEmbedding) terminates and is correct and performs at most the stated number of operations → there exists a program of the machine that, on every input satisfying Algorithm 2's Input block, halts with an output satisfying its Output block within the stated bound; reason: the paper does not fix its subroutines (fast GCD, remainder trees, CRT, characteristic polynomials, modular composition), so the claim is read as existence of an implementation of the stated contract
--   - encoding: Õ(φ) of Section 3: there exist C, κ > 0 such that for all inputs the cost is ≤ C φ log(exp(1) + φ)^κ → ∃ K κ > 0 quantified before the field and every input; cost ≤ softOBound K κ φ = K·φ·Real.log(Real.exp 1 + φ)^κ, natural log of q = Fintype.card F; reason: verbatim Section 3 definition over the domain of all valid inputs; the constant is named K because C is Polynomial.C
--   - encoding: p a prime greater than 3, q = p^e, Fq (with an Fp-basis and multiplication table when given as input) → an arbitrary finite field F : Type with 3 < ringChar F and q = Fintype.card F; algorithmic items receive q as an integer and no Fp-basis; reason: same fields; the algebraic lemmas require no field presentation, and algorithmic items use the uniform field-operation model without a basis
--   - encoding: polynomials, integers and field elements as algorithm inputs and outputs → inputs: a polynomial g as its coefficients 0..natDegree g; outputs: a polynomial is read from any finite coefficient list (trailing zeros allowed, IsPolyVal); deg as natDegree in the cost (natDegree 0 = 0); reason: fixed documented layout shared by every item; the reading of an output is exact equality of polynomials
-- source:
--   Spaenlehauer, Deterministic Root-Finding over Finite Fields with Elliptic Curves, arXiv:2610.32508 (version held, sha256 c72ee273…), p. 19, Proposition 4.7 (Algorithm 2, p. 18)

import Mathlib
import Definitions.Def_EllipticRootFinding_Online_Machine
import Definitions.Def_EllipticRootFinding_Online_Complexity

open Polynomial

namespace EllipticRootFinding.Online

/-- Proposition 4.7 (p. 19) for Algorithm 2 (FiniteFieldEmbedding, p. 18), read as: one program of
the machine meets Algorithm 2's Input/Output contract on every finite field `F` of characteristic
`> 3`, within `K · φ · log(e + φ)^κ` counted field operations,
`φ = log q · (deg f · log q + deg h)`, with `K, κ > 0` fixed before all inputs.

Input layout `[q, h, f, β]`. Output `[u₀, u₁, v₀, v₁]` with `u₀, u₁` monic, `u₀ u₁ = f`,
`deg v₀ < deg u₀`, `deg v₁ < deg u₁`, `v₀² ≡ h mod u₀` and `β v₁² ≡ h mod u₁`. -/
theorem proposition_4_7 :
    ∃ P : Program, ∃ K κ : ℝ, 0 < K ∧ 0 < κ ∧
      ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F], 3 < ringChar F →
      ∀ (h f : F[X]), f.Monic → f.Splits → f.Separable → IsCoprime f h →
      ∀ (β : F), ¬ IsSquare β →
        Computes P
          (Val.ofList [Val.int (Fintype.card F : ℤ), polyVal h, polyVal f, Val.fld β])
          (fun out => ∃ (u₀ u₁ v₀ v₁ : F[X]) (w₁ w₂ w₃ w₄ : Val F),
            out = Val.ofList [w₁, w₂, w₃, w₄] ∧
            IsPolyVal w₁ u₀ ∧ IsPolyVal w₂ u₁ ∧ IsPolyVal w₃ v₀ ∧ IsPolyVal w₄ v₁ ∧
            u₀.Monic ∧ u₁.Monic ∧ u₀ * u₁ = f ∧
            v₀.degree < u₀.degree ∧ v₁.degree < u₁.degree ∧
            u₀ ∣ v₀ ^ 2 - h ∧ u₁ ∣ C β * v₁ ^ 2 - h)
          (softOBound K κ (Real.log (Fintype.card F) *
            ((f.natDegree : ℝ) * Real.log (Fintype.card F) + (h.natDegree : ℝ)))) := by sorry

end EllipticRootFinding.Online
