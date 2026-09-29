-- Prove2me | Theorems.Thm_CannonFloydParry_Y_conj_eq_Y_succ
-- name    : CannonFloydParry.Y_conj_eq_Y_succ
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-17T20:43:12.169161+00:00
-- url     : https://prove2.me/theorems/599f0054-4444-421b-a57b-04d929b0d3bb
-- title:
--   Line (3.2): $Y_k^{-1} Y_n Y_k = Y_{n+1}$ in $F_1$ for $k < n$
-- statement:
--   In the presented group $F_1$, with $Y_0 = A$ and $Y_n = A^{-(n-1)} B A^{n-1}$ for
--   $n \ge 1$: for all natural numbers $k < n$,
--   $$Y_k^{-1}\, Y_n\, Y_k = Y_{n+1}.$$
--   So the elements $Y_n$ of $F_1$ satisfy the defining relations of $F_2$, and $X_n \mapsto Y_n$
--   extends to a homomorphism $F_2 \to F_1$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 3, pp. 225–226, line (3.2)

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Definitions.Def_CannonFloydParry_Presentations
import Mathlib

namespace CannonFloydParry

/-- Line (3.2), p. 225: in `F₁`, `Yₖ⁻¹ Yₙ Yₖ = Yₙ₊₁` for `k < n`, so `Xₙ ↦ Yₙ` extends to a
homomorphism `F₂ → F₁`. -/
theorem Y_conj_eq_Y_succ (k n : ℕ) (hkn : k < n) : (Y k)⁻¹ * Y n * Y k = Y (n + 1) := by
  sorry

end CannonFloydParry
