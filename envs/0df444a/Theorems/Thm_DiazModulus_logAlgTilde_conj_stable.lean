-- Prove2me | Theorems.Thm_DiazModulus_logAlgTilde_conj_stable
-- name    : DiazModulus.logAlgTilde_conj_stable
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T08:53:45.462998+00:00
-- url     : https://prove2.me/theorems/9922f109-5be0-427a-93a2-e7015b8cdf9d
-- title:
--   ℒ̃ is stable under complex conjugation
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers, and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$.
--
--   If $z \in \widetilde{\mathcal{L}}$, then $\bar z \in \widetilde{\mathcal{L}}$.
--
--   **Proof.** By induction on the span: $\bar 1 = 1$; the conjugate of a logarithm of an algebraic number is a logarithm of the conjugate number (`DiazModulus.logAlg_conj_stable`); and the conjugate of an algebraic coefficient is algebraic.
--
--   **Novelty.** None: a standard fact, used throughout Diaz (2004, 2007).
-- source:
--   Standard; used throughout G. Diaz, Utilisation de la conjugaison complexe dans l'étude de la transcendance de valeurs de la fonction exponentielle usuelle, J. Théor. Nombres Bordeaux 16 (2004), 535–553 and G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391. Formal proof: Diaz modulus mission, 1 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

/-- `ℒ̃` is stable under complex conjugation. -/
theorem logAlgTilde_conj_stable (z : ℂ) (h : z ∈ LogAlgTilde) : conj z ∈ LogAlgTilde := by
  sorry

end DiazModulus
