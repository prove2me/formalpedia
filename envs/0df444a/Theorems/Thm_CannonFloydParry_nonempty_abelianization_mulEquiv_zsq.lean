-- Prove2me | Theorems.Thm_CannonFloydParry_nonempty_abelianization_mulEquiv_zsq
-- name    : CannonFloydParry.nonempty_abelianization_mulEquiv_zsq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-15T19:29:10.686178+00:00
-- url     : https://prove2.me/theorems/6abafd73-b0b3-4b78-b749-d1fcef03adad
-- title:
--   The abelianization of $F$ is $\mathbb{Z} \oplus \mathbb{Z}$
-- statement:
--   The quotient of Thompson's group $F$ by its commutator subgroup is isomorphic to
--   $\mathbb{Z} \oplus \mathbb{Z}$.
--
--   In the source the isomorphism is induced by the homomorphism sending $f \in F$ to the pair
--   $(a,b)$ of integers for which the right derivative of $f$ at $0$ is $2^{a}$ and the left
--   derivative of $f$ at $1$ is $2^{b}$. The assertion here is that some isomorphism exists, not
--   that it is this particular one.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, Theorem 4.1, p. 228, second sentence

import Definitions.Def_CannonFloydParry
import Mathlib

namespace CannonFloydParry

theorem nonempty_abelianization_mulEquiv_zsq :
    Nonempty (Abelianization F ≃* Multiplicative (ℤ × ℤ)) := by
  sorry

end CannonFloydParry
