-- Prove2me | solution 1 for isRegularLocalRing_localization_atPrime_of_isStandardSmooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/038df739-6a45-5e08-891c-85d6db1ce5eb

import Mathlib
import Theorems.Thm_Algebra_IsStandardSmooth_exists_isStandardSmoothOfRelativeDimension_of_field
import Theorems.Thm_isRegularLocalRing_localization_atPrime_mvPolynomial
import Theorems.Thm_isRegularLocalRing_localization_atPrime_of_etale_of_comap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_isRegularLocalRing_localization_atPrime_of_isStandardSmooth
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

theorem solution
    (k B : Type*) [Field k] [CommRing B] [Algebra k B]
    [Algebra.IsStandardSmooth k B] (q : Ideal B) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  classical
  obtain ⟨m, hm⟩ :=
    Algebra.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension_of_field (k := k) (B := B)
  haveI := hm
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial m k B
  letI : Algebra (MvPolynomial (Fin m) k) B := g.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin m) k) B := hg
  haveI : IsScalarTower k (MvPolynomial (Fin m) k) B :=
    IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm
  have hbase := isRegularLocalRing_localization_atPrime_mvPolynomial k m
    (q.comap (algebraMap (MvPolynomial (Fin m) k) B))
  exact isRegularLocalRing_localization_atPrime_of_etale_of_comap
    (MvPolynomial (Fin m) k) B q hbase

end S_isRegularLocalRing_localization_atPrime_of_isStandardSmooth
end P2MW
export P2MW.S_isRegularLocalRing_localization_atPrime_of_isStandardSmooth (solution)
