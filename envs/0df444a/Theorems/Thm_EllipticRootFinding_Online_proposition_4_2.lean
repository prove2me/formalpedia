-- Prove2me | Theorems.Thm_EllipticRootFinding_Online_proposition_4_2
-- name    : EllipticRootFinding.Online.proposition_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:03:32.009286+00:00
-- url     : https://prove2.me/theorems/9bf4655f-d302-4c2a-8f29-8dab0d1b3a32
-- title:
--   Proposition 4.2 — Algorithm 1 (2-adic factorization by evaluation) in Õ(m(deg f log q + deg h)) operations
-- statement:
--   Let $F$ be a finite field with $q$ elements and characteristic greater than $3$. Algorithm 1 (TwoadicFactoWithEval) receives an integer $0 \le m \le v_2(q-1)$, a polynomial $h \in F[X]$, a monic split separable $f \in F[X]$ coprime with $h$ such that $v_2(\mathrm{order}(h(x))) \le m$ for every root $x$ of $f$, and $\beta \in F^\times$ with $v_2(\mathrm{order}(\beta)) = m$. It must output a finite set $S \subset [\![0, 2^m - 1]\!]$ and monic nonconstant polynomials $f^{(j)}$, $j \in S$, with $\prod_{j \in S} f^{(j)} = f$ and
--   $$f^{(j)} = \gcd\Bigl(f,\ \prod_{\zeta \in F,\ h(\zeta) \neq 0,\ \mathrm{order}(h(\zeta)\beta^{-j})\ \text{odd}} (X - \zeta)\Bigr).$$
--   The statement is: there are one program $P$ of the machine and constants $K, \kappa > 0$ such that, for every such field and input, $P$ halts with such an output after at most $K\varphi\log(e+\varphi)^\kappa$ counted operations, where $\varphi = m(\deg f \cdot \log q + \deg h)$.
--
--   This factorization by the 2-adic part of the order of $h(\alpha)$ is the first stage of Algorithm 2.
--
--   **Formalization Note.** Input layout $[q, m, h, f, \beta]$; output: a list of pairs $[j, f^{(j)}]$ with pairwise distinct $j$; $\gcd$ is the normalized (monic) gcd of `Polynomial`; orders are `orderOf` in $F$.
--
--   Differences from the source:
--   - encoding: arithmetic operations in Fq (model of computation not specified) → one finite program (List Instr) independent of the field, run over every finite field F of characteristic > 3; field +, −, ×, inverse (0⁻¹ = 0) and zero-test cost 1; the constants 0 and 1, copies of field registers and all integer instructions (unbounded integers) are free; no integer-to-field cast, no other field constant; input and output are Val values in a fixed self-delimiting register layout; reason: the paper counts only operations in Fq; the machine makes 'algorithm' and 'operation' precise without granting a non-uniform family or free field information
--   - reading: Algorithm 1 (TwoadicFactoWithEval) terminates and is correct and performs at most the stated number of operations → there exists a program of the machine that, on every input satisfying Algorithm 1's Input block, halts with an output satisfying its Output block within the stated bound; reason: the paper does not fix its subroutines (fast GCD, remainder trees, CRT, characteristic polynomials, modular composition), so the claim is read as existence of an implementation of the stated contract
--   - encoding: Õ(φ) of Section 3: there exist C, κ > 0 such that for all inputs the cost is ≤ C φ log(exp(1) + φ)^κ → ∃ K κ > 0 quantified before the field and every input; cost ≤ softOBound K κ φ = K·φ·Real.log(Real.exp 1 + φ)^κ, natural log of q = Fintype.card F; reason: verbatim Section 3 definition over the domain of all valid inputs; the constant is named K because C is Polynomial.C
--   - encoding: p a prime greater than 3, q = p^e, Fq (with an Fp-basis and multiplication table when given as input) → an arbitrary finite field F : Type with 3 < ringChar F and q = Fintype.card F; algorithmic items receive q as an integer and no Fp-basis; reason: same fields; the algebraic lemmas require no field presentation, and algorithmic items use the uniform field-operation model without a basis
--   - encoding: polynomials, integers and field elements as algorithm inputs and outputs → inputs: a polynomial g as its coefficients 0..natDegree g; outputs: a polynomial is read from any finite coefficient list (trailing zeros allowed, IsPolyVal); deg as natDegree in the cost (natDegree 0 = 0); reason: fixed documented layout shared by every item; the reading of an output is exact equality of polynomials
--   - encoding: output: a finite set S and a finite set of pairs {(j, f^(j))}_{j∈S}; GCD; β ∈ F×q; order(·) → a list of pairs [j, f^(j)] whose j are pairwise distinct; gcd of Polynomial F (normalized, monic); β ≠ 0; orderOf in F; reason: same objects in a fixed layout
-- source:
--   Spaenlehauer, Deterministic Root-Finding over Finite Fields with Elliptic Curves, arXiv:2610.32508 (version held, sha256 c72ee273…), p. 14, Proposition 4.2 (Algorithm 1, p. 15)

import Mathlib
import Definitions.Def_EllipticRootFinding_Online_Machine
import Definitions.Def_EllipticRootFinding_Online_Complexity

open Polynomial

namespace EllipticRootFinding.Online

/-- Proposition 4.2 (p. 14) for Algorithm 1 (TwoadicFactoWithEval, p. 15), read as: one program of
the machine meets Algorithm 1's Input/Output contract on every finite field `F` of characteristic
`> 3`, within `K · φ · log(e + φ)^κ` counted field operations, `φ = m (deg f · log q + deg h)`,
with `K, κ > 0` fixed before all inputs.

Input layout `[q, m, h, f, β]`. Output: a list of pairs `[j, f⁽ʲ⁾]`, the `j` pairwise distinct
(the set `S`), each `j ∈ ⟦0, 2^m − 1⟧`, each `f⁽ʲ⁾` monic nonconstant and equal to
`GCD(f, ∏_{ζ ∈ F, h(ζ) ≠ 0, order(h(ζ)β^{−j}) odd} (X − ζ))` (normalized, i.e. monic, gcd), and
`∏_{j ∈ S} f⁽ʲ⁾ = f`. -/
theorem proposition_4_2 :
    ∃ P : Program, ∃ K κ : ℝ, 0 < K ∧ 0 < κ ∧
      ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F], 3 < ringChar F →
      ∀ (m : ℕ), m ≤ padicValNat 2 (Fintype.card F - 1) →
      ∀ (h f : F[X]), f.Monic → f.Splits → f.Separable → IsCoprime f h →
      (∀ x : F, f.IsRoot x → padicValNat 2 (orderOf (h.eval x)) ≤ m) →
      ∀ (β : F), β ≠ 0 → padicValNat 2 (orderOf β) = m →
        Computes P
          (Val.ofList [Val.int (Fintype.card F : ℤ), Val.int (m : ℤ), polyVal h, polyVal f,
            Val.fld β])
          (fun out => ∃ (ps : List (ℤ × F[X])) (ws : List (Val F)),
            out = Val.ofList ws ∧
            List.Forall₂ (fun w jg => ∃ pv : Val F, w = Val.ofList [Val.int jg.1, pv] ∧
              IsPolyVal pv jg.2) ws ps ∧
            (ps.map Prod.fst).Nodup ∧
            (∀ jg ∈ ps, 0 ≤ jg.1 ∧ jg.1 ≤ 2 ^ m - 1 ∧ jg.2.Monic ∧ 0 < jg.2.natDegree ∧
              jg.2 = gcd f (∏ ζ ∈ Finset.univ.filter
                (fun ζ : F => h.eval ζ ≠ 0 ∧ Odd (orderOf (h.eval ζ * β ^ (-jg.1)))),
                (X - C ζ))) ∧
            (ps.map Prod.snd).prod = f)
          (softOBound K κ ((m : ℝ) * ((f.natDegree : ℝ) * Real.log (Fintype.card F) +
            (h.natDegree : ℝ)))) := by sorry

end EllipticRootFinding.Online
