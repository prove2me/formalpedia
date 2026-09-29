-- Prove2me | Theorems.Thm_ColemanMandula_lemma8_translation_plus_internal
-- name    : ColemanMandula.lemma8_translation_plus_internal
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-24T05:03:04.673979+00:00
-- url     : https://prove2.me/theorems/3b131df7-6a75-45e1-9b63-db61cc11eb75
-- title:
--   Coleman–Mandula Lemma 8: $B(p)=a_\mu p^\mu+b$
-- statement:
--   Assume particle finiteness, weak elastic analyticity and occurrence of scattering, and let $B\in\mathfrak B_S$. Then there exist a constant four-vector $a$ and an infinitesimal internal symmetry transformation $b$ (Hermitian, commuting with the Lorentz action on every hyperboloid) such that
--   $$B_k(p)=(a\cdot p)\,\mathbf 1+b_k(p)\qquad\text{for every hyperboloid }H_k\text{ and every }p\in H_k,$$
--   i.e. $B$ is the sum of an infinitesimal translation and an infinitesimal internal symmetry transformation.
-- source:
--   S. Coleman and J. Mandula, All Possible Symmetries of the S Matrix, Phys. Rev. 159 (1967) 1251-1256, https://doi.org/10.1103/PhysRev.159.1251, p. 1256, Lemma 8 (Eq. (30))

import Definitions.Def_ColemanMandula_Scattering

open Matrix
open scoped Kronecker

namespace ColemanMandula

theorem lemma8_translation_plus_internal (D : ScatteringData)
    (hfin : D.ParticleFinite) (hana : D.ElasticAnalytic) (hscat : D.ScatteringOccurs)
    (B : D.Multiplier) (hB : D.IsSymMultiplier B) :
    ∃ (a : FourVec) (b : D.Multiplier), D.IsInternal b ∧
      ∀ k, ∀ p ∈ massShell (D.mass k), B k p = ((mdot a p : ℝ) : ℂ) • 1 + b k p := by
  sorry

end ColemanMandula
