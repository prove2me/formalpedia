-- Prove2me | Theorems.Thm_DiazModulus_dalag_cor_12_22
-- name    : DiazModulus.dalag_cor_12_22
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T10:29:54.468518+00:00
-- url     : https://prove2.me/theorems/fdabc010-80b2-4365-b646-5e2b7e6a1784
-- title:
--   DALAG Cor. 12.22: if M = Σₖ eₖNₖ has entries in ℒ̃, with e₁, …, eₘ Q̄-free and algebraic Nₖ, the rank of Σₖ XₖNₖ over Q̄(X₁, …, Xₘ) is at most 2 rank M
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $M$ be a $d \times \ell$ matrix with entries in $\widetilde{\mathcal L}$, and suppose that $M = \sum_{k=1}^m e_k N_k$ with $e_1, \dots, e_m \in \mathbb C$ linearly independent over $\overline{\mathbb Q}$ and $N_1, \dots, N_m$ matrices of size $d \times \ell$ with algebraic entries. Let $N(X) = \sum_{k=1}^m X_k N_k$, a matrix over the field $\overline{\mathbb Q}(X_1, \dots, X_m)$ of rational functions in $m$ variables. Then
--   $$\operatorname{rank}_{\overline{\mathbb Q}(X_1, \dots, X_m)} N(X) \le 2 \operatorname{rank} M.$$
--   The rank of $N(X)$ is the structural rank of $M$ over $\overline{\mathbb Q}$ in the sense of DALAG §12.1.4; the statement holds for every such presentation of $M$.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Cor. 12.22 (p. 436), deduced from Th. 12.20 (D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Cor. 1; on the platform DiazModulus.roy_rank_bound) as Cor. 12.18 is deduced from Th. 12.17 (p. 433); the structural rank (§12.1.4, pp. 426–427) is written through a presentation M = Σ eₖNₖ. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dalag_cor_12_22 {d l m : ℕ} (M : Matrix (Fin d) (Fin l) ℂ) (hM : ∀ i j, M i j ∈ LogAlgTilde)
    (e : Fin m → ℂ) (he : LinearIndependent (↥Qbar) e) (N : Fin m → Matrix (Fin d) (Fin l) ↥Qbar)
    (hMN : M = ∑ k, e k • (N k).map ((↑) : ↥Qbar → ℂ)) :
    (∑ k, (algebraMap (MvPolynomial (Fin m) ↥Qbar) (FractionRing (MvPolynomial (Fin m) ↥Qbar))
        (MvPolynomial.X k)) •
      (N k).map (algebraMap ↥Qbar (FractionRing (MvPolynomial (Fin m) ↥Qbar)))).rank ≤ 2 * M.rank := by
  sorry

end DiazModulus
