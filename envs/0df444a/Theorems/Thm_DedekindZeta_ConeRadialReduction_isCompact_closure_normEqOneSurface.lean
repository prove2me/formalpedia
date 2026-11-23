-- Prove2me | Theorems.Thm_DedekindZeta_ConeRadialReduction_isCompact_closure_normEqOneSurface
-- name    : DedekindZeta.ConeRadialReduction.isCompact_closure_normEqOneSurface
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:30:45.589916+00:00
-- url     : https://prove2.me/theorems/5c788dec-b9c9-4f00-8b45-b5994dc89d11
-- title:
--   Cone Radial Reduction: is Compact closure norm Eq One Surface
-- statement:
--   The norm-1 surface fundamental domain is **relatively compact**: its closure
--   is compact.  the standard treatment states that the norm-1 surface fundamental domain
--   is compact, but Mathlib realises `mixedEmbedding.fundamentalCone K` via the
--   *half-open* `ZSpan.fundamentalDomain` (a half-open parallelepiped, see
--   `fundamentalCone` and the `Set.Ico 0 1` faces of `ZSpan.fundamentalDomain`).
--   Consequently the literal slice `normEqOneSurface K` is **not closed** (the faces
--   where a logarithmic coordinate hits `1` are genuine limit points that are
--   excluded), so it is not compact as a subset; only its closure is.  This mirrors
--   Mathlib's own choice to prove only `IsBounded` (never `IsCompact`) for the
--   analogous half-open set `normLeOne K` (`fundamentalCone.isBounded_normLeOne`).
--   The faithful, true encoding of the standard treatment's compactness here is therefore
--   compactness of the closure, which is what downstream finiteness/integrability
--   arguments actually use.  Proof: closed (`isClosed_closure`) and bounded (the
--   surface is contained in the bounded `normLeOne K`), via Heine–Borel.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L105-L108
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeRadialReduction.lean#L105-L108

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}

theorem DedekindZeta.ConeRadialReduction.isCompact_closure_normEqOneSurface : IsCompact (closure (normEqOneSurface K)) := by sorry
