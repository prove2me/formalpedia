-- Prove2me | Theorems.Thm_AutomorphicForm_norm_algebraNorm_eq_prod_norm_baseChangeAlgEquiv_apply
-- name    : AutomorphicForm.norm_algebraNorm_eq_prod_norm_baseChangeAlgEquiv_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/d87f1910-cb28-50db-82b4-bee9251fc137
-- title:
--   Norm on L⊗_K Kᵥ is the product of local norms
-- statement:
--   Let $K$ and $L$ be number fields (fields in the lowest universe, each carrying a `NumberField` structure) with $L$ a $K$-algebra, and let $v$ be a height-one prime of the ring of integers $\mathcal{O}_K$, the set $v.\mathrm{Extension}\,(\mathcal{O}_L)$ of height-one primes $w$ of $\mathcal{O}_L$ whose contraction to $\mathcal{O}_K$ is $v$ being assumed finite. Let $\alpha$ be an element of the $v$-adic base change $L \otimes_K K_v$, where $K_v$ denotes `v.adicCompletion K`. Then the norm of the algebra norm $N_{L\otimes_K K_v / K_v}(\alpha)$, that is of the determinant of multiplication by $\alpha$ on $L \otimes_K K_v$ viewed as a $K_v$-module, measured by the absolute value of $K_v$, equals the finite product over the primes $w$ above $v$ of the norms, in the completions $L_w$, of the components of the image of $\alpha$ under `HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv`, the $L$-algebra isomorphism $L \otimes_K K_v \cong \prod_{w \mid v} L_w$ obtained from the base change of the canonical semialgebra map to the product of completions, shown there to be bijective.
--
--   This is the classical compatibility of the norm of the semi-local algebra $L \otimes_K K_v \cong \prod_{w\mid v} L_w$ with the normalised absolute values, $\|N(\alpha)\|_v = \prod_{w\mid v}\|\alpha_w\|_w$, stated here for a finite set of extensions of $v$ as an ordinary finite product. It is used in the estimates on integrals of automorphic forms over double cosets of upper-triangular matrices.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_norm_algebraNorm_eq_prod_norm_baseChangeAlgEquiv_apply.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.norm_algebraNorm_eq_prod_norm_baseChangeAlgEquiv_apply
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) [Fintype (v.Extension (𝓞 L))]
    (α : L ⊗[K] v.adicCompletion K) :
    ‖Algebra.norm (v.adicCompletion K) α‖ =
      ∏ w : v.Extension (𝓞 L), ‖HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v α w‖ := by sorry
