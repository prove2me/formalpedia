-- Prove2me | Theorems.Thm_CODATA_expansion_rules
-- name    : CODATA.expansion_rules
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-21T01:38:41.146265+00:00
-- url     : https://prove2.me/theorems/4ec0db95-d1bb-4666-b58a-05b2a5c9bbd1
-- title:
--   Expansion of uncertainties preserves correlations
-- statement:
--   Let V be a covariance matrix with positive diagonal entries and fs a
--   family of positive factors. The expansion of V by the constant factor
--   3.9 multiplies every entry by 3.9 squared. Every correlation
--   coefficient of V is unchanged by that expansion, and more generally
--   the correlation coefficient of a pair of entries is unchanged
--   whenever the two members carry equal factors. This is the algebra
--   underlying the statement of the 2022 CODATA report that the expansion
--   factors are applied to the uncertainties of all the data of a group so
--   as to maintain their original relative weights and correlations; the
--   constant factor 3.9 is the expansion factor of the separate adjustment
--   of the sixteen values of the Newtonian constant of gravitation.
-- source:
--   P. J. Mohr, D. B. Newell, B. N. Taylor and E. Tiesinga, CODATA recommended values of the fundamental physical constants: 2022, J. Phys. Chem. Ref. Data 54, 033105 (2025), doi 10.1063/5.0279860; Rev. Mod. Phys. 97, 025002 (2025), doi 10.1103/RevModPhys.97.025002, section XII: the expansion factors are applied to all the data of a group to maintain their original relative weights and correlations; the factor 3.9 reduces all normalized residuals of the sixteen values of G to two or less.

import Mathlib
import Definitions.Def_CODATA_lsa
import Definitions.Def_CODATA_uncert
import Definitions.Def_CODATA_values

/-!
# Expansion of uncertainties preserves correlations

Section XII of the 2022 CODATA report applies expansion factors to the
uncertainties of groups of input data (1.7 and 2.5 in the main
adjustment; 3.9 for the sixteen values of the Newtonian constant of
gravitation) in order to reduce all normalized residuals to two or
less, and it states that the factors are applied to all the data of a
group so as to maintain their original relative weights and
correlations. This milestone formalizes the underlying algebra of the
covariance matrix under such an expansion: the expanded covariance is
the entrywise product by the pairwise products of the factors; a common
factor leaves every correlation coefficient unchanged; and more
generally the correlation coefficient of a pair is unchanged whenever
the two members carry equal factors. The constant factor 39/10 is the
expansion factor 3.9 of the separate adjustment of the Newtonian
constant of gravitation. This milestone is proved on the way to the
goal theorem `CODATA.codata_self_consistent`.
-/

namespace CODATA

/-- Let V be a covariance matrix with positive diagonal entries and fs
a family of positive factors. The expansion of V by the constant
factor 39/10 multiplies every entry by (39/10)^2; every correlation
coefficient of V is unchanged by that expansion; and more generally,
whenever two entries carry equal factors, their correlation
coefficient is unchanged by the expansion. -/
theorem expansion_rules {N : ℕ} (V : Matrix (Fin N) (Fin N) ℝ)
    (fs : Fin N → ℝ) (hfs : ∀ k, 0 < fs k) (hV : ∀ k, 0 < V k k) :
    (∀ k l, expandD (fun _ => 39/10) V k l = (39/10) * (39/10) * V k l) ∧
      (∀ i j, corr (expandD (fun _ => 39/10) V) i j = corr V i j) ∧
      (∀ i j, fs i = fs j → corr (expandD fs V) i j = corr V i j) := by
  sorry

end CODATA
