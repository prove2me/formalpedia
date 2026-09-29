-- Prove2me | Theorems.Thm_AutomorphicForm_whittakerCoefficient_inv_star_mul_apply_det_eq_star_whittakerCoefficient_mul
-- name    : AutomorphicForm.whittakerCoefficient_inv_star_mul_apply_det_eq_star_whittakerCoefficient_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/c047bb8a-a359-50f7-93ab-fd739aae0972
-- title:
--   Whittaker coefficient of a conjugated, determinant-twisted automorphic function
-- statement:
--   Let $K$ be a number field, and let `pins : CarrierPins K` be a package of carrier data for $\mathrm{GL}_2$ over $K$ (a measurable space and a measure on $\mathrm{GL}_2(\mathbb{A}_K)$, a subset $D$ of that group, a subgroup $Z$ of the ideles, a family of level subgroups indexed by ideals of $\mathcal{O}_K$, elements indexed by the finite places, and a measurable space `nS` and measure $\nu$ on $\mathbb{A}_K$). Let $\psi$ be an additive character of the adele ring $\mathbb{A}_K$ with values in $\mathbb{C}$ which is unitary in the sense that $\lVert\psi(x)\rVert=1$ for every $x \in \mathbb{A}_K$; let $\varphi : \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ and $\chi : \mathbb{A}_K^\times\to\mathbb{C}$ be arbitrary functions (no character or automorphy condition on either), and let $a \in K$ and $g \in \mathrm{GL}_2(\mathbb{A}_K)$. Here the $\psi$-Whittaker coefficient of $\varphi$ at $a$ and $g$ is the Bochner integral $\int_{\mathbb{A}_K}\varphi\bigl(n(x)g\bigr)\,\psi\bigl(-(a x)\bigr)\,d\nu(x)$, with $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $a$ mapped into $\mathbb{A}_K$ by the structure map. The assertion is that the $\psi^{-1}$-Whittaker coefficient of the function $h \mapsto \overline{\varphi(h)}\,\chi(\det h)$ at $a$ and $g$ equals $\overline{W^{\psi}_a(\varphi)(g)}\cdot\chi(\det g)$. No integrability hypothesis is imposed; the identity holds with the Lean convention for the Bochner integral.
--
--   This is the elementary compatibility of Whittaker coefficients with complex conjugation and with a twist by a function of the determinant: conjugating the automorphic function and inverting the additive character reproduces the conjugate coefficient, up to the factor $\chi(\det g)$. It is used when assembling Rankin–Selberg test data, where the properties of a partner function of the shape $\overline{\varphi}\cdot(\chi\circ\det)$ must be read off from those of $\varphi$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_whittakerCoefficient_inv_star_mul_apply_det_eq_star_whittakerCoefficient_mul.lean

import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem AutomorphicForm.whittakerCoefficient_inv_star_mul_apply_det_eq_star_whittakerCoefficient_mul
    (K : Type) [Field K] [NumberField K] (pins : CarrierPins K)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (hψ : ∀ x : AdeleRing (𝓞 K) K, ‖ψ x‖ = 1)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (χ : (AdeleRing (𝓞 K) K)ˣ → ℂ) (a : K) (g : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ⁻¹ (fun h : AdelicGL2 (𝓞 K) K => (starRingEnd ℂ) (φ h) * χ (Matrix.GeneralLinearGroup.det h)) a g =
      (starRingEnd ℂ) (whittakerCoefficient K pins ψ φ a g) * χ (Matrix.GeneralLinearGroup.det g) := by sorry
