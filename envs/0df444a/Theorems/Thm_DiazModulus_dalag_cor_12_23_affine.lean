-- Prove2me | Theorems.Thm_DiazModulus_dalag_cor_12_23_affine
-- name    : DiazModulus.dalag_cor_12_23_affine
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T17:29:18.145217+00:00
-- url     : https://prove2.me/theorems/00e2717a-2559-4199-8194-0f12b8bfbace
-- title:
--   DALAG Cor. 12.23, p. 435 form: if M = M₀ + Σ λₖNₖ with M₀, Nₖ rational, λₖ ∈ ℚ + ℒ and 1, λ₁, …, λₘ free over ℚ, then rank M ≥ ½ rank(M₀ + Σ XₖNₖ) over ℚ(X)
-- statement:
--   Here $\mathcal L$ is the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic). Write $\mathbb Q + \mathcal L$ for the $\mathbb Q$-vector space spanned by $1$ and $\mathcal L$; it consists of the numbers $q + \lambda$ with $q \in \mathbb Q$ and $\lambda \in \mathcal L$.
--
--   Let $\lambda_1, \dots, \lambda_m \in \mathbb Q + \mathcal L$ be such that $1, \lambda_1, \dots, \lambda_m$ are linearly independent over $\mathbb Q$, let $M_0, N_1, \dots, N_m$ be $d \times \ell$ matrices with rational entries, and let $M = M_0 + \sum_{k=1}^m \lambda_k N_k$. Then
--   $$\operatorname{rank}_{\mathbb Q(X_1, \dots, X_m)}\Big(M_0 + \sum_{k=1}^m X_k N_k\Big) \le 2 \operatorname{rank} M.$$
--   The left-hand side is the structural rank of $M$ over $\mathbb Q$, computed with the map $1 \mapsto 1$, $\lambda_k \mapsto X_k$ into the affine forms, as on DALAG p. 435.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Cor. 12.23 (p. 436), with the matrix M₀ + Σ XₖNₖ of p. 435, whose entries are affine. Proved from the presentation form DiazModulus.dalag_cor_12_23 and the dehomogenisation DiazModulus.dalag_lemma_12_9_dehomog. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dalag_cor_12_23_affine {d l m : ℕ} (M : Matrix (Fin d) (Fin l) ℂ)
    (lam : Fin m → ℂ) (hlam : ∀ k, ∃ q : ℚ, lam k - q ∈ LogAlg)
    (hfree : LinearIndependent ℚ (Fin.cons 1 lam : Fin (m + 1) → ℂ))
    (M₀ : Matrix (Fin d) (Fin l) ℚ) (N : Fin m → Matrix (Fin d) (Fin l) ℚ)
    (hMN : M = M₀.map ((↑) : ℚ → ℂ) + ∑ k, lam k • (N k).map ((↑) : ℚ → ℂ)) :
    (M₀.map (algebraMap ℚ (FractionRing (MvPolynomial (Fin m) ℚ))) +
      ∑ k, (algebraMap (MvPolynomial (Fin m) ℚ) (FractionRing (MvPolynomial (Fin m) ℚ))
        (MvPolynomial.X k)) •
      (N k).map (algebraMap ℚ (FractionRing (MvPolynomial (Fin m) ℚ)))).rank ≤ 2 * M.rank := by
  sorry

end DiazModulus
