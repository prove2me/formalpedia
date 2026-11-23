-- Prove2me | Theorems.Thm_DedekindZeta_ConeMellinBridge_integrableOn_idealThetaKernel_mul_norm_cpow
-- name    : DedekindZeta.ConeMellinBridge.integrableOn_idealThetaKernel_mul_norm_cpow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:50:42.453531+00:00
-- url     : https://prove2.me/theorems/74d1cc78-a127-483d-ba0c-1bab53e61e41
-- title:
--   Cone Mellin Bridge: integrable On ideal Theta Kernel mul norm cpow
-- statement:
--   **Integrability of the integral-ideal cone Mellin integrand on `Re s > 1`.**
--
--   Transports the proved fractional-ideal integrability
--   `DedekindZeta.integrable_indicator_mixedThetaKernel_mul_norm_cpow` along
--   `Theta.idealThetaKernel_eq_mixed` to the integral ideal `𝔞`, in the
--   `IntegrableOn … fundamentalCone` form required by
--   `coneMellin_idealThetaKernel_eq_mellin`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeMellinBridge.lean#L128-L136
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeMellinBridge.lean#L128-L136

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Definitions.Def_DedekindZeta_ConeMellinBridge
set_option autoImplicit true
open MeasureTheory NumberField NumberField.mixedEmbedding
open scoped Real nonZeroDivisors
open DedekindZeta DedekindZeta.ConeMellinBridge
open DedekindZeta.ConeRadialReduction DedekindZeta.MellinPrinciple
variable (K : Type*) [Field K] [NumberField K]
variable {K}

theorem DedekindZeta.ConeMellinBridge.integrableOn_idealThetaKernel_mul_norm_cpow (𝔞 : Ideal (𝓞 K)) {s : ℂ}
    (hs : 1 < s.re) :
    IntegrableOn
      (fun x => Theta.idealThetaKernel K 𝔞 x * (mixedEmbedding.norm x : ℂ) ^ s)
      (mixedEmbedding.fundamentalCone K) (DedekindZeta.mixedMulHaar K) := by sorry
