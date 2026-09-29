-- Prove2me | Theorems.Thm_CannonFloydParry_of_succ_eq_conj_F2
-- name    : CannonFloydParry.of_succ_eq_conj_F2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-17T20:41:25.120141+00:00
-- url     : https://prove2.me/theorems/5d59eca8-780b-4f96-b5f6-6550080ab0b1
-- title:
--   In $F_2$, $X_{n} = X_0^{-(n-1)} X_1 X_0^{\,n-1}$
-- statement:
--   In the presented group $F_2$, for every natural number $n$,
--   $$X_{n+1} = X_0^{-n}\, X_1\, X_0^{\,n},$$
--   i.e. the source's $X_n = X_0^{-(n-1)} X_1 X_0^{n-1}$ for $n \ge 1$. In particular $X_0$ and $X_1$
--   generate $F_2$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 3, p. 225 (proof of Theorem 3.1, surjectivity)

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Definitions.Def_CannonFloydParry_Presentations
import Mathlib

namespace CannonFloydParry

/-- Theorem 3.1, surjectivity ingredient: in `F₂`, `Xₙ = X₀^{-(n-1)} X₁ X₀^{n-1}` for `n ≥ 1`,
so `X₀` and `X₁` generate `F₂`. -/
theorem of_succ_eq_conj_F2 (n : ℕ) :
    (PresentedGroup.of (n + 1) : F2)
      = (PresentedGroup.of 0 ^ n)⁻¹ * PresentedGroup.of 1 * PresentedGroup.of 0 ^ n := by
  sorry

end CannonFloydParry
