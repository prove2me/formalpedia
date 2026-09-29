-- Prove2me | Theorems.Thm_DiazModulus_div_not_mem_logAlgTilde_of_sfe
-- name    : DiazModulus.div_not_mem_logAlgTilde_of_sfe
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T18:03:14.688749+00:00
-- url     : https://prove2.me/theorems/802c7dc6-80fc-4bbd-ba2e-8024d59f84e6
-- title:
--   Under the strong four exponentials conjecture, a transcendental quotient of two elements of ℒ̃ is not in ℒ̃
-- statement:
--   Assume the strong four exponentials conjecture (`DiazModulus.StrongFourExponentials`). Let $\Lambda_1, \Lambda_2 \in \widetilde{\mathcal L}$, the $\overline{\mathbb Q}$-vector space spanned by $1$ and the logarithms of algebraic numbers, and suppose that $\Lambda_1$ and $\Lambda_2/\Lambda_1$ are transcendental. Then
--
--   $$\Lambda_2/\Lambda_1 \notin \widetilde{\mathcal L}.$$
--
--   This is Waldschmidt's Consequence 1.7. The case $\Lambda_2 = 1$ is his Consequence 1.6: $1/\Lambda \notin \widetilde{\mathcal L}$ for every transcendental $\Lambda \in \widetilde{\mathcal L}$. At $\Lambda = i\pi$ this gives $1/(i\pi) \notin \widetilde{\mathcal L}$ under the conjecture, a stronger form of `DiazModulus.recip_pi_not_log_of_sfe`. The proof applies the conjecture to $x = (1, \Lambda_2/\Lambda_1)$ and $y = (\Lambda_1, 1)$.
-- source:
--   Known: M. Waldschmidt, Variations on the six exponentials theorem, in Algebra and Number Theory (R. Tandon, ed.), Hindustan Book Agency, 2005, Consequences 1.6 and 1.7, conditional on the strong four exponentials conjecture (Conjecture 1.5 there). Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi).

import Definitions.Def_DiazModulus

namespace DiazModulus

theorem div_not_mem_logAlgTilde_of_sfe (hS : StrongFourExponentials) (L₁ L₂ : ℂ)
    (h₁ : L₁ ∈ LogAlgTilde) (h₂ : L₂ ∈ LogAlgTilde)
    (ht₁ : Transcendental ℚ L₁) (ht : Transcendental ℚ (L₂ / L₁)) :
    L₂ / L₁ ∉ LogAlgTilde := by
  sorry

end DiazModulus
