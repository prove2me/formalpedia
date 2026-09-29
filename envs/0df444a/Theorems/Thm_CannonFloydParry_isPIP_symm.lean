-- Prove2me | Theorems.Thm_CannonFloydParry_isPIP_symm
-- name    : CannonFloydParry.isPIP_symm
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T20:04:18.551982+00:00
-- url     : https://prove2.me/theorems/9a249950-9f6a-4efa-b1c7-a332d0fa114d
-- title:
--   p. 249 — the inverse of a PIP homeomorphism of Δₙ is PIP
-- statement:
--   If a homeomorphism $f$ of $\Delta_n$ is piecewise integral projective (integral projective on each simplex of some integral subdivision), so is $f^{-1}$. The subdivision for $f^{-1}$ is not required to be related to that of $f$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 7, p. 249, PIP homeomorphisms

import Mathlib
import Definitions.Def_CannonFloydParry_PIP

namespace CannonFloydParry

theorem isPIP_symm {n : ℕ} {f : Simplex n ≃ₜ Simplex n} (hf : IsPIP f) : IsPIP f.symm := by
  sorry

end CannonFloydParry
