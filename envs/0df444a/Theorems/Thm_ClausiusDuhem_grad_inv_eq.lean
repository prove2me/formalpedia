-- Prove2me | Theorems.Thm_ClausiusDuhem_grad_inv_eq
-- name    : ClausiusDuhem.grad_inv_eq
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:31:21.477051+00:00
-- url     : https://prove2.me/theorems/bdad79bf-43b4-4ea9-8e20-367b73eeb76d
-- title:
--   $\nabla(1/T)=-\nabla T/T^2$
-- statement:
--   Let $T:\mathbb R^3\to\mathbb R$ be differentiable at $x$ with $T(x)\neq0$. Then
--   $$\nabla\Big(\frac1T\Big)(x)=-\frac{1}{T(x)^2}\,\nabla T(x).$$
--
--   This is the step that turns $\mathbf q\cdot\nabla(1/T)$ into $-\mathbf q\cdot\nabla T/T^2$ in the derivation of the internal-energy form.
-- source:
--   Wikipedia, "Clausius–Duhem inequality", revision oldid=1182390552, https://en.wikipedia.org/w/index.php?title=Clausius%E2%80%93Duhem_inequality&oldid=1182390552, section "Clausius–Duhem inequality in terms of specific internal energy", Proof (index-notation computation of the gradient of 1/T).

import Definitions.Def_ClausiusDuhem_thermo_process

namespace ClausiusDuhem
theorem grad_inv_eq (T : Space → ℝ) (x : Space)
    (hT : DifferentiableAt ℝ T x) (hTx : T x ≠ 0) :
    grad (fun y => (T y)⁻¹) x = -(1 / T x ^ 2) • grad T x := by sorry
end ClausiusDuhem
