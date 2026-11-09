-- Prove2me | Theorems.Thm_CliffordCert_Optimal_isotropic_completion
-- name    : CliffordCert.Optimal.isotropic_completion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:34:48.038307+00:00
-- url     : https://prove2.me/theorems/ca2ee262-d4fa-48d7-9a2c-6bee086eb476
-- title:
--   Lemma 3 — isotropic completion
-- statement:
--   Let $A$ be a totally isotropic subspace of a finite-dimensional nondegenerate binary symplectic space. If $h=\dim A$, there is a nondegenerate ambient subspace $E$ with
--   $$A\subseteq E,\qquad \dim E=2h.$$
--   The zero-dimensional case is included. This is the dimension-preserving completion ingredient for repairing pieces of a radical.
--
--   Differences from the source:
--   - encoding: an arbitrary N-dimensional binary vector space → Fin N → ZMod 2 with an arbitrary alternating nondegenerate bilinear form when needed; reason: choosing coordinates is a linear isomorphism and changes no instance
-- source:
--   Hyunho Cha, Jungwoo Lee, STOC 2027 submission #226 (October 2026), p. 11, Lemma 3 (PDF p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/226.pdf

import Definitions.Def_CliffordCert_Optimal_symplectic
set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal

namespace CliffordCert.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem isotropic_completion {N : ℕ} (B : Form N) (hB : IsSymplectic B)
    (A : Submodule F₂ (Binary N)) (hA : IsIsotropic B A) :
    ∃ E : Submodule F₂ (Binary N), A ≤ E ∧ Nondegenerate B E ∧
      Module.finrank F₂ E = 2 * Module.finrank F₂ A := by sorry
end CliffordCert.Optimal
