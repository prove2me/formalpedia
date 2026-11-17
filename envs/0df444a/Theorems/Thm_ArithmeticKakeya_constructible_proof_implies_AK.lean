-- Prove2me | Theorems.Thm_ArithmeticKakeya_constructible_proof_implies_AK
-- name    : ArithmeticKakeya.constructible_proof_implies_AK
-- status  : Open
-- author  : @Lucas
-- created : 2026-11-16T21:57:58.09921+00:00
-- url     : https://prove2.me/theorems/36a1cfff-f478-4552-b863-73acf7c6292c
-- title:
--   A constructible proof of score $s$ implies $\mathrm{AK}(s)$
-- statement:
--   The Katz–Tao reduction: if $(R,T)$ is a forcing $X$-set for a constructible graph $G$, no element of $X$ has coordinate-sum zero, and $|T|<n(G)$, then $\mathrm{AK}\big((m(G)+|R|)/(n(G)-|T|)\big)$ holds. It combines the counting lemma (lower bound on copies of $G$) with the forcing property (upper bound), turning a combinatorial configuration into an arithmetic Kakeya exponent.
-- source:
--   https://epoch.ai/frontiermath/open-problems/arithmetic-kakeya (The link to arithmetic Kakeya)

import Mathlib
import Definitions.Def_ArithmeticKakeya_grid
import Definitions.Def_ArithmeticKakeya_forcing
import Definitions.Def_ArithmeticKakeya_ak

namespace ArithmeticKakeya
theorem constructible_proof_implies_AK
    {X : Finset (ℤ × ℤ)} (hX : ∀ x ∈ X, x.1 + x.2 ≠ 0)
    (G : ConstructibleGraph X) (R : List (List ℕ → ℤ × ℤ)) (T : List (List ℕ))
    (hXT : IsXSet G R T) (hF : Forces G R T) (ht : T.length < n G) :
    AK ((m G + R.length : ℝ) / (n G - T.length : ℝ)) := by sorry
end ArithmeticKakeya
