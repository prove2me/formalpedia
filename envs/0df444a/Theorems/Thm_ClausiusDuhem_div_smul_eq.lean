-- Prove2me | Theorems.Thm_ClausiusDuhem_div_smul_eq
-- name    : ClausiusDuhem.div_smul_eq
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:28:51.589978+00:00
-- url     : https://prove2.me/theorems/3ec56f2e-bd30-47c1-90be-b77cc1d0ebbb
-- title:
--   $\nabla\cdot(\varphi\mathbf v)=\varphi\,\nabla\cdot\mathbf v+\mathbf v\cdot\nabla\varphi$
-- statement:
--   Let $\varphi:\mathbb R^3\to\mathbb R$ and $\mathbf v:\mathbb R^3\to\mathbb R^3$ be differentiable at the point $x$. Then
--   $$\nabla\cdot(\varphi\,\mathbf v)(x)=\varphi(x)\,\nabla\cdot\mathbf v(x)+\mathbf v(x)\cdot\nabla\varphi(x).$$
--
--   This product rule converts the divergence of $\mathbf q/T$ and of $\rho\eta\mathbf v$ into the terms appearing in the differential forms of the Clausius–Duhem inequality.
-- source:
--   Wikipedia, "Clausius–Duhem inequality", revision oldid=1182390552, https://en.wikipedia.org/w/index.php?title=Clausius%E2%80%93Duhem_inequality&oldid=1182390552, section "Clausius–Duhem inequality in terms of specific internal energy", Proof, first line (the identity used).

import Definitions.Def_ClausiusDuhem_thermo_process

namespace ClausiusDuhem
theorem div_smul_eq (φ : Space → ℝ) (v : Space → Fin 3 → ℝ) (x : Space)
    (hφ : DifferentiableAt ℝ φ x) (hv : DifferentiableAt ℝ v x) :
    div (fun y => φ y • v y) x = φ x * div v x + dot (v x) (grad φ x) := by sorry
end ClausiusDuhem
