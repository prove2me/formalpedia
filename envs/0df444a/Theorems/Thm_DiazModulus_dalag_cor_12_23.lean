-- Prove2me | Theorems.Thm_DiazModulus_dalag_cor_12_23
-- name    : DiazModulus.dalag_cor_12_23
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T14:06:33.208308+00:00
-- url     : https://prove2.me/theorems/db2914f2-8295-45b1-9e73-f9f77fc0aaff
-- title:
--   DALAG Cor. 12.23: if M = Σₖ eₖNₖ with e₁, …, eₘ ∈ ℚ + ℒ linearly independent over ℚ and rational matrices Nₖ, the rank of Σₖ XₖNₖ over ℚ(X₁, …, Xₘ) is at most 2 rank M
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $M$ be a complex $d \times \ell$ matrix, let $e_1, \dots, e_m \in \mathbb C$ be linearly independent over $\mathbb Q$ with each $e_k \in \mathbb Q + \mathcal L$ (that is, $e_k - q_k \in \mathcal L$ for some $q_k \in \mathbb Q$), and let $N_1, \dots, N_m$ be $d \times \ell$ matrices with rational entries such that $M = \sum_{k=1}^m e_k N_k$. Let $N(X) = \sum_{k=1}^m X_k N_k$, a matrix over the field $\mathbb Q(X_1, \dots, X_m)$ of rational functions in $m$ variables. Then
--   $$\operatorname{rank}_{\mathbb Q(X_1, \dots, X_m)} N(X) \le 2 \operatorname{rank} M.$$
--   The rank of $N(X)$ is the structural rank of $M$ over $\mathbb Q$ in the sense of DALAG §12.1.4; every matrix with entries in $\mathbb Q + \mathcal L$ has such a presentation, and the statement holds for each of them.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Cor. 12.23 (p. 436), for the structural rank over ℚ (§12.1.4, p. 426), in the presentation form: M = Σₖ eₖNₖ with e₁, …, eₘ ∈ ℚ + ℒ linearly independent over ℚ and rational Nₖ, the structural rank being the rank of Σₖ XₖNₖ over ℚ(X₁, …, Xₘ). Proved from Cor. 12.22 (p. 436; on the platform DiazModulus.dalag_cor_12_22) and Baker's theorem (DALAG, Th. 1.6), proved on the platform as Schanuel.baker_linear_forms_in_logarithms: by Baker's theorem the eₖ are linearly independent over Q̄ (as on p. 435), so M = Σₖ eₖNₖ is also a presentation over Q̄, and the rank of Σₖ XₖNₖ is the same over ℚ(X₁, …, Xₘ) and over Q̄(X₁, …, Xₘ). Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dalag_cor_12_23 {d l m : ℕ} (M : Matrix (Fin d) (Fin l) ℂ)
    (e : Fin m → ℂ) (he : LinearIndependent ℚ e) (heL : ∀ k, ∃ q : ℚ, e k - q ∈ LogAlg)
    (N : Fin m → Matrix (Fin d) (Fin l) ℚ)
    (hMN : M = ∑ k, e k • (N k).map ((↑) : ℚ → ℂ)) :
    (∑ k, (algebraMap (MvPolynomial (Fin m) ℚ) (FractionRing (MvPolynomial (Fin m) ℚ))
        (MvPolynomial.X k)) •
      (N k).map (algebraMap ℚ (FractionRing (MvPolynomial (Fin m) ℚ)))).rank ≤ 2 * M.rank := by
  sorry

end DiazModulus
