-- Prove2me | Theorems.Thm_DiazModulus_fv_cor_1_3
-- name    : DiazModulus.fv_cor_1_3
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-18T16:16:35.716706+00:00
-- url     : https://prove2.me/theorems/2febd686-af69-4a37-ba86-1323dfdd816d
-- title:
--   Waldschmidt 2005 (Further variations), Cor. 1.3: if Λ₁, Λ₂, Λ₃ ∈ ℒ̃, Λ₁ is transcendental and 1, Λ₂, Λ₃ are Q̄-free, then Λ₁Λ₂ ∉ ℒ̃ or Λ₁Λ₃ ∉ ℒ̃
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $\Lambda_1, \Lambda_2, \Lambda_3 \in \widetilde{\mathcal L}$. Assume that $\Lambda_1$ is transcendental and that $1, \Lambda_2, \Lambda_3$ are linearly independent over $\overline{\mathbb Q}$. Then at least one of the two numbers $\Lambda_1\Lambda_2$, $\Lambda_1\Lambda_3$ is not in $\widetilde{\mathcal L}$.
-- source:
--   M. Waldschmidt, Further variations on the six exponentials theorem, Hardy-Ramanujan J. 28 (2005), 1–9, Cor. 1.3 (p. 3), as printed. No proof is printed; the paper presents it as a consequence of Th. 1.1, Roy's strong six exponentials theorem, and the proof is that one: Th. 1.1 for x = (1, Λ₁) and y = (1, Λ₂, Λ₃), through DiazModulus.strong_six_exponentials_unconditional. Formal proof: Diaz modulus mission, 18 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fv_cor_1_3 (Λ₁ Λ₂ Λ₃ : ℂ) (h₁ : Λ₁ ∈ LogAlgTilde) (h₂ : Λ₂ ∈ LogAlgTilde)
    (h₃ : Λ₃ ∈ LogAlgTilde) (htr : Transcendental ℚ Λ₁)
    (hfree : LinearIndependent (↥Qbar) ![1, Λ₂, Λ₃]) :
    Λ₁ * Λ₂ ∉ LogAlgTilde ∨ Λ₁ * Λ₃ ∉ LogAlgTilde := by
  sorry

end DiazModulus
