-- Prove2me | Theorems.Thm_CannonFloydParry_exists_homeomorph_image_of_isIntegralProjective
-- name    : CannonFloydParry.exists_homeomorph_image_of_isIntegralProjective
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T20:03:53.739761+00:00
-- url     : https://prove2.me/theorems/f4b68417-6191-4e02-91f3-b7fbf983b182
-- title:
--   p. 249 — an integral projective map is a homeomorphism onto its image
-- statement:
--   If $f$ is integral projective on $U \subseteq \Delta_n$, then $f$ restricted to $U$ is a homeomorphism from $U$ onto $f(U)$: there is a homeomorphism $e \colon U \to f(U)$ with $e(x) = f(x)$ for every $x \in U$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 7, p. 249, integral projective maps

import Mathlib
import Definitions.Def_CannonFloydParry_PIP

namespace CannonFloydParry

theorem exists_homeomorph_image_of_isIntegralProjective {n : ℕ} {U : Set (Simplex n)}
    {f : Simplex n → Simplex n} (hf : IsIntegralProjective U f) :
    ∃ e : U ≃ₜ f '' U, ∀ x : U, (e x : Simplex n) = f x := by
  sorry

end CannonFloydParry
