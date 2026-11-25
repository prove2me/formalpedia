-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_OrthogonalComplementGenusMass_isLatIn_push_iff_isLattice
-- name    : Formalism.L2.SG.Pf.OrthogonalComplementGenusMass.isLatIn_push_iff_isLattice
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:23:04.648476+00:00
-- url     : https://prove2.me/theorems/239e7aed-0443-4039-973f-d4211d24a789
-- title:
--   Orthogonal Complement Genus Mass: is Lat In push iff is Lattice
-- statement:
--   The Orthogonal Complement Genus Mass construction uses the is Lat In push iff is Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExtensionIdentityOfMemCompl.lean#L99-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExtensionIdentityOfMemCompl.lean#L99-L112

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NondegenerateOnOrthCompl
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExtensionIdentityOfMemCompl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.OrthogonalComplementGenusMass
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G9
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.L2.SG.Pf.OrthogonalComplementGenusMass.isLatIn_push_iff_isLattice {X : Submodule K V} (L : Submodule (𝓞 K) ↥X) :
    IsLatIn X (push X L) ↔ Submodule.IsLattice K L := by sorry
