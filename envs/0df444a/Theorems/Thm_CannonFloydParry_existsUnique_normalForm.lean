-- Prove2me | Theorems.Thm_CannonFloydParry_existsUnique_normalForm
-- name    : CannonFloydParry.existsUnique_normalForm
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-16T21:14:25.987487+00:00
-- url     : https://prove2.me/theorems/366d4a92-f891-42b5-9738-5765a9d7fa38
-- title:
--   Corollary-Definition 2.7: the unique normal form in $F$
-- statement:
--   **Corollary-Definition 2.7.** Every element $f \ne 1$ of Thompson's group $F$ can be
--   written in **exactly one** way as
--   $$f = X_0^{b_0} X_1^{b_1} \cdots X_n^{b_n} \, X_n^{-a_n} \cdots X_1^{-a_1} X_0^{-a_0}$$
--   with $n$ and all $a_k$, $b_k$ nonnegative integers such that (i) exactly one of $a_n$ and $b_n$
--   is nonzero, and (ii) if $a_k > 0$ and $b_k > 0$ for some $k < n$, then $a_{k+1} > 0$ or
--   $b_{k+1} > 0$.
--
--   Uniqueness is asserted of the exponent data itself: there is exactly one pair of finite lists
--   satisfying the two conditions whose word is $f$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, section 2 p. 224, Corollary-Definition 2.7

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Mathlib

namespace CannonFloydParry

theorem existsUnique_normalForm {f : UI ≃o UI} (hf : f ∈ F) (hne : f ≠ 1) :
    ∃! p : List ℕ × List ℕ, IsNormalFormData p.1 p.2 ∧ f = word p.2 * (word p.1)⁻¹ := by
  sorry

end CannonFloydParry
