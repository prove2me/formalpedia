-- Prove2me | Theorems.Thm_F3SubsetSum_proposition_4_9
-- name    : F3SubsetSum.proposition_4_9
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T12:31:04.498708+00:00
-- url     : https://prove2.me/theorems/ae845cab-52a6-49a2-85a7-27eab9304bf5
-- title:
--   Proposition 4.9 — $V/N\cong S/J$ when $\Phi_{m,D}$ is surjective
-- statement:
--   Let $q\ge3$ be prime, $(A,b)$ an instance, $D\ge2$, and suppose $\Phi_{m,D}$ is surjective. Fix **any** family $Q_{i,\alpha}\in R_{D-2}$ satisfying (30) and let $N\subseteq S$ be the relation space built from it by (31)–(38). Define $\pi:V\to S/J$ by $\pi(v)=[v]_J$. Then
--
--   $$\pi \text{ is surjective and }\ker\pi=N,$$
--
--   so $V/N\cong S/J$. The decoder computes $N$ by linear algebra, and this proposition says that $V/N$ is the quotient algebra of Corollary 4.2.
--
--   Differences from the source:
--   - encoding: x^α in R_D; Q_{i,α} ∈ R_{D−2} used inside S → x^α is the basis vector Pi.single α 1 of the coefficient space R_D; Q_{i,α} is lifted to S by its reduced representative; reason: R_D has the basis of reduced monomials (p.18); the reduced representative is the paper's identification of R with reduced polynomials
--   - encoding: N is N_r once N_{r+1} = N_r → N is the supremum ⨆_r N_r of the increasing chain; reason: an increasing chain that stabilises has its stable value as supremum
--   - encoding: ker(π) = N with π defined on V → v ∈ N ↔ (v ∈ V ∧ [v]_J = 0) for all v ∈ S; reason: states ker π = N together with N ⊆ V
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, Proposition 4.9, p.21 (objects pp.19–20)

import Mathlib
import Definitions.Def_F3SubsetSum_QuotientAlgebra
import Definitions.Def_F3SubsetSum_TruncatedRing
import Definitions.Def_F3SubsetSum_RelationSpace

namespace F3SubsetSum

/-- **Proposition 4.9** (Kothari, Metger, O'Donnell, Shutty, Wu, arXiv:2609.40321v1,
Proposition 4.9, p.21): "If Φ_{m,D} is surjective, then V/N ≅ S/J. More precisely, define
π: V → S/J by π(v) = [v]_J and then π is surjective with ker(π) = N."

Setting (§4.2, pp.19–20): `q ≥ 3` prime, an instance `(A, b)`, an integer `D ≥ 2`, and **any**
family `Q_{i,α} ∈ R_{D−2}` (one for each reduced degree-`D` monomial `x^α`) with
`Σ_i L_i² Q_{i,α} = x^α` in `R_D` (eq. (30)); `N` is the relation space built from this family by
(31)–(38), and `V = ⟨ℳ_{<D}⟩`. Conclusion: every class of `S/J` is `[v]_J` for some `v ∈ V`, and
the vectors `v` with `v ∈ N` are exactly those `v ∈ V` with `[v]_J = 0`.

**Formalization Note** `x^α ∈ R_D` is the basis vector `Pi.single α 1` of the coefficient space
`R_D`. "ker(π) = N" includes `N ⊆ V`. -/
theorem proposition_4_9 (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (ZMod q)) (b : Fin m → ZMod q) (D : ℕ) (hD : 2 ≤ D)
    (hsurj : Function.Surjective (Phi (ZMod q) q (cols A) D))
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (hQ : ∀ α, Phi (ZMod q) q (cols A) D (Q α) = Pi.single α 1) :
    (∀ y : MvPolynomial (Fin n) (ZMod q) ⧸ idealJ A b,
        ∃ v ∈ lowSpan q n D, Ideal.Quotient.mk (idealJ A b) v = y) ∧
      ∀ v : MvPolynomial (Fin n) (ZMod q),
        v ∈ relSpace A b D Q ↔ (v ∈ lowSpan q n D ∧ Ideal.Quotient.mk (idealJ A b) v = 0) := by sorry

end F3SubsetSum
