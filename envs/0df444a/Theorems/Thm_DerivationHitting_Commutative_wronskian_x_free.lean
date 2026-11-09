-- Prove2me | Theorems.Thm_DerivationHitting_Commutative_wronskian_x_free
-- name    : DerivationHitting.Commutative.wronskian_x_free
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:51.588207+00:00
-- url     : https://prove2.me/theorems/2d46b56e-4280-439b-9d5c-e2ab10fdd55d
-- title:
--   Lemma 3.1 — The D-Wronskian determinant is x-free
-- statement:
--   Let $F$ be a characteristic-zero field, $n,q\in\mathbb N$, and $b_i\in F(t)$. Let $g_1,\ldots,g_q\in F[x_1,\ldots,x_n]$ have derivative-closed $F$-linear span. With $D_b=\partial_t+\sum_i b_i\partial_{x_i}$ and $W_{D_b}$ its determinant Wronskian, there is $a(t)\in F(t)$ such that
--   $$
--    W_{D_b}(g_1,\ldots,g_q)=a(t)\quad\text{in }F(t)[x_1,\ldots,x_n].
--   $$
--   Thus the determinant is independent of every $x$ variable. The statement includes the source's degree-ordered derivative-space basis, but does not require a normalization of its endpoints. It consequently also covers constant families and the empty family, whose determinant is $1$.
--
--   Differences from the source:
--   - encoding: variables indexed by 1,…,n → variables indexed by Fin n, with integer parameter i.val+1; reason: this is a bijective reindexing and the first kernel is nonzero
--   - generalization: a degree-ordered basis of a derivative space, with the section normalizations → any finite family of t-free polynomials whose F-linear span is derivative-closed; reason: every source basis is such a family; changing the basis changes the Wronskian by a constant determinant, while a dependent family has zero Wronskian
--   - encoding: independent of x → equality to a constant multivariate polynomial with coefficient in F(t); reason: this expresses exactly independence from all x variables, not independence from t
-- source:
--   Shubham Bhardwaj, Foram Lakhani, Partha Mukhopadhyay, Ramprasad Saptharishi, Pratik Shastri, Amit Sinhababu, STOC 2027 submission #577 (October 2026), p. 12, Lemma 3.1 and §3 standing basis setup; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/577.pdf

import Definitions.Def_DerivationHitting_Commutative_DifferentialData

namespace DerivationHitting.Commutative
theorem wronskian_x_free {F : Type*} [Field F] [CharZero F] {n q : ℕ}
    (b : Fin n → RatFunc F) (g : Fin q → MvPolynomial (Fin n) F)
    (hclosed : derivativeClosed g) :
    ∃ a : RatFunc F, derivationWronskian b g = MvPolynomial.C a := by sorry
end DerivationHitting.Commutative
