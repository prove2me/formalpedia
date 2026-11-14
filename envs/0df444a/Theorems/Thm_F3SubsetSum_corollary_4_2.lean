-- Prove2me | Theorems.Thm_F3SubsetSum_corollary_4_2
-- name    : F3SubsetSum.corollary_4_2
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T12:28:49.23132+00:00
-- url     : https://prove2.me/theorems/052363f5-7eea-4432-9454-c089d14dd7d9
-- title:
--   Corollary 4.2 — unique candidate iff $\dim(S/J)=1$, and recovery of $s$
-- statement:
--   Let $q\ge3$ be prime, $(A,b)\in\mathbb F_q^{n\times m}\times\mathbb F_q^m$, $S=\mathbb F_q[x_1,\dots,x_n]$, $J$ the ideal (27) and $\mathcal C$ the candidate set (26). Then
--
--   $$\mathcal C \text{ is a singleton}\iff \dim_{\mathbb F_q}(S/J)=1 ,$$
--
--   and if $\mathcal C=\{s\}$, then $[1]_J$ is a basis of $S/J$ and
--
--   $$[x_j]_J=s_j\,[1]_J\qquad\text{for every } j\in[n].$$
--
--   This is how the quotient decoder reads the secret off the quotient algebra.
--
--   Differences from the source:
--   - encoding: [1]_J is a basis of S/J → [1]_J ≠ 0 and the span of [1]_J is S/J; reason: a one-element family is a basis exactly when it is nonzero and spanning
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, Corollary 4.2, p.18

import Mathlib
import Definitions.Def_F3SubsetSum_QuotientAlgebra

namespace F3SubsetSum

open MvPolynomial

/-- **Corollary 4.2** (Kothari, Metger, O'Donnell, Shutty, Wu, arXiv:2609.40321v1, Corollary 4.2,
p.18): "There is a unique candidate s for Problem 1.5 if and only if dim(S/J) = 1. In that case,
[1]_J is a basis of S/J, and the jth coordinate of s is determined by [x_j]_J = s_j[1]_J."

For an instance `(A, b) ∈ F_q^{n×m} × F_q^m`, `q ≥ 3` prime, with `S = F_q[x_1, …, x_n]`, `J` the
ideal (27) and `𝒞` the candidate set (26): `𝒞` is a singleton iff `dim_{F_q}(S/J) = 1`; and if
`𝒞 = {s}`, then `[1]_J` is nonzero and spans `S/J`, and `[x_j]_J = s_j [1]_J` for every `j`.

**Formalization Note** "[1]_J is a basis" is stated as "`[1]_J ≠ 0` and `[1]_J` spans `S/J`". -/
theorem corollary_4_2 (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (ZMod q)) (b : Fin m → ZMod q) :
    ((∃ s, candidates A b = {s}) ↔
        Module.finrank (ZMod q) (MvPolynomial (Fin n) (ZMod q) ⧸ idealJ A b) = 1) ∧
      ∀ s : Fin n → ZMod q, candidates A b = {s} →
        Ideal.Quotient.mk (idealJ A b) 1 ≠ 0 ∧
        Submodule.span (ZMod q) {Ideal.Quotient.mk (idealJ A b) 1} = ⊤ ∧
        ∀ j : Fin n, Ideal.Quotient.mk (idealJ A b) (X j) =
          s j • Ideal.Quotient.mk (idealJ A b) 1 := by sorry

end F3SubsetSum
