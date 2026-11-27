-- Prove2me | solution 1 for fd_point_assembly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:34:52.796649+00:00
-- url     : https://prove2.me/submissions/91e1479c-939d-442f-8dd1-b7ce6804a18c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_DivLeExpOfAbsLogSubLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_FourierJacobiDifferentiable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_FdPointAssembly
import Theorems.Thm_PIW_FdPA_borel_flag_translate
import Theorems.Thm_PIW_FdPA_chartNorm_nonneg
import Theorems.Thm_PIW_FdPA_chartNorm_smul
import Theorems.Thm_PIW_FdPA_chart_zero_eq_alt
import Theorems.Thm_PIW_FdPA_fourierJacobi_boundaryEq
import Theorems.Thm_PIW_FdPA_fourierJacobi_bounded
import Theorems.Thm_PIW_FdPA_fourierJacobi_differentiable
import Theorems.Thm_PIW_FdPA_fundamentalDomain_of_parts
import Theorems.Thm_PIW_FdPA_normFactor_pos_alt
import Theorems.Thm_PIW_FdPA_orthonormal_domain
import Theorems.Thm_PIW_FdPA_unitary_domain


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open PIW.FdPA
theorem _root_.solution {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] : ReciprocityTheory.ChartRestriction.G.FD.ShortVectorBound (E := E) → ReciprocityTheory.ChartRestriction.G.FD.OrthonormalFlagTranslate (E := E) → ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartNormControl (E := E) → ReciprocityTheory.ChartRestriction.G.FD.NearSupremumTransference (E := E) → ReciprocityTheory.ChartRestriction.G.FD.SchwarzLemmaBall → ReciprocityTheory.ChartRestriction.G.FD.OrthonormalShortVectorBound (E := E) → ReciprocityTheory.ChartRestriction.G.FD.IsotropicCoefficientSplitting (E := E) → ReciprocityTheory.ChartRestriction.G.FD.NoShortVectorLowerBound (E := E) → ReciprocityTheory.ChartRestriction.G.FD.UnitaryUnipotentMove (E := E) → ReciprocityTheory.ChartRestriction.G.FD.FundamentalDomainPointBound (E := E) :=
  fun _ h0 h1 h2 h3 h4 _ _ h7 =>
    fundamentalDomain_of_parts fourierJacobi_differentiable fourierJacobi_boundaryEq fourierJacobi_bounded orthonormal_domain unitary_domain borel_flag_translate
      chartNorm_smul chartNorm_nonneg normFactor_pos_alt chart_zero_eq_alt h0 h1 h2 h3 h4 h7
