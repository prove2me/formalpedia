-- Prove2me | Theorems.Thm_DerivationHitting_Commutative_Supplement_wronskian_factorization
-- name    : DerivationHitting.Commutative.Supplement.wronskian_factorization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:57:02.379649+00:00
-- url     : https://prove2.me/theorems/2e84643b-7d66-4f3c-a51f-c25dd74215dd
-- title:
--   Theorem 3.2 — Upper unitriangular Wronskian factorization
-- statement:
--   Let F be any characteristic-zero field and let f∈F[x₁,…,xₙ]. Let g₁,…,gᵣ be a degree-filtration-compatible basis of the whole ordinary derivative space of f, ordered by total degree. For any rational kernel tuple bᵢ(t), form D=∂ₜ+Σᵢbᵢ(t)∂ₓᵢ and the matrix W_D whose row m is (Dᵐgⱼ)ⱼ, for 0≤m<r. Then there exist matrices R over F(t) and H over F[x₁,…,xₙ] such that
--
--   $$W_D=R(t)H(x),\qquad H_{ij}=0\ (i>j),\qquad H_{ii}=1.$$
--
--   The identity is in the matrix ring over F(t)[x]. Both triangularity and every diagonal entry are asserted; the polynomial factor has no dependence on t. The rational kernels are unrestricted. Nonzero constants require no normalization, and r=0 gives the empty matrix identity.
--
--   This companion theorem asserts a matrix factorization, in addition to the determinant statement already published. The basis reading follows the source's earlier-index derivative relations; a merely degree-sorted basis can fail, as documented with the rational one-variable cubic counterexample in the moderation notes.
--
--   Differences from the source:
--   - encoding: variables numbered 1,…,n → variables Fin n with source index i.val+1; reason: a bijective change of indices preserves every coefficient
--   - reading: §3 chooses a degree-ordered basis and uses strictly earlier-index derivative relations → the chosen basis is compatible with every degree-filtration piece as well as ordered by degree; reason: mere sorting is insufficient; the source argument requires filtration compatibility, which is available for every derivative space
--   - generalization: the setup normalizes the first basis vector to 1 and the last to f → any degree-compatible basis, including unnormalized bases for nonzero constants and the empty basis for f=0; reason: the factorization is invariant under these scalar basis normalizations and specializes to the source setup
--   - encoding: W_D=R(t)F(x) → both factors are embedded into F(t)[x] before matrix multiplication; reason: the types enforce that R has no x dependence and the polynomial factor has no t dependence
-- source:
--   Shubham Bhardwaj, Foram Lakhani, Partha Mukhopadhyay, Ramprasad Saptharishi, Pratik Shastri, Amit Sinhababu, STOC 2027 submission #577 (October 2026). Canonical submission artifact, not proceedings publication; no arXiv pin. Printed page = PDF page throughout 1–29. pp.12–14, Theorem 3.2, especially equations (3.3)–(3.4).

import Definitions.Def_DerivationHitting_Commutative_Supplement_WronskianData

namespace DerivationHitting.Commutative.Supplement

theorem wronskian_factorization {F : Type*} [Field F] [CharZero F] {n r : ℕ}
    (f : MvPolynomial (Fin n) F) (g : Fin r → MvPolynomial (Fin n) F)
    (hg : DegreeCompatibleBasis f g) (b : Fin n → RatFunc F) :
    ∃ (R : Matrix (Fin r) (Fin r) (RatFunc F))
      (H : Matrix (Fin r) (Fin r) (MvPolynomial (Fin n) F)),
      derivationWronskianMatrix b g =
        R.map MvPolynomial.C * H.map rationalPolynomial ∧
      (∀ i j, j < i → H i j = 0) ∧ (∀ i, H i i = 1) := by sorry

end DerivationHitting.Commutative.Supplement
