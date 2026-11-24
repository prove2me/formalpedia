-- Prove2me | Theorems.Thm_Arxiv1507_03491_local_equation_unique_solvability
-- name    : Arxiv1507_03491.local_equation_unique_solvability
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T17:26:22.554847+00:00
-- url     : https://prove2.me/theorems/c792750e-3aa7-4543-9282-89d24a29098e
-- title:
--   Theorem 5.1: unique solvability of the local integral equation
-- statement:
--   Let $\operatorname{Re}k>0$, $\operatorname{Im}k\ge0$, $\operatorname{Re}\alpha\ge0$ and $M_0>0$. Let $g$ be Hölder continuous on $\Gamma_0=(-M_0,M_0)$ with some exponent $r>0$. Then the local integral equation
--
--   $$-\tfrac12\sigma(x)+ik\alpha\,S_{\Gamma_0}[\sigma](x,0)=g(x)\qquad(x\in\Gamma_0)$$
--
--   has a solution $\sigma\in C(\Gamma_0)$, and any two solutions that are continuous on the closed segment $[-M_0,M_0]$ coincide there.
--
--   This is the well-posedness of the local integral equation (3.9) on which the impedance scheme rests.
--
--   **Formalization Note** The paper writes $\alpha$ for both the Hölder exponent and the impedance constant; the exponent is called $r$ here. $C(\Gamma_0)$ is read as the continuous functions on the closed segment $[-M_0,M_0]$, the Banach space on which the paper's Fredholm argument works. Uniqueness is therefore asserted only among densities continuous up to the endpoints; this is weaker than uniqueness among all functions continuous on the open segment $\Gamma_0$. The standing assumptions $\operatorname{Re}k>0$, $\operatorname{Im}k\ge0$ and $\operatorname{Re}\alpha\ge0$ come from Section 1.
-- source:
--   Lai, Greengard and O'Neil, A new hybrid integral representation for frequency domain scattering in layered media, arXiv:1507.03491v2 (2015), claim c010; Section 5, Theorem 5.1 and Remark 3, PDF pp. 12–13

import Mathlib
import Definitions.Def_Arxiv1507_03491_Basic

open MeasureTheory Filter Topology Set
open scoped ContDiff NNReal

namespace Arxiv1507_03491

theorem local_equation_unique_solvability (k alpha : ℂ) (hk : 0 < k.re) (hk' : 0 ≤ k.im)
    (halpha : 0 ≤ alpha.re) (M0 : ℝ) (hM0 : 0 < M0) (g : ℝ → ℂ)
    (hg : ∃ (C r : ℝ≥0), 0 < r ∧ HolderOnWith C r g (Ioo (-M0) M0)) :
    (∃ sigma : ℝ → ℂ, ContinuousOn sigma (Icc (-M0) M0) ∧
      ∀ x ∈ Ioo (-M0) M0,
        -(1 / 2) * sigma x + Complex.I * k * alpha * singleLayer k M0 sigma x 0 = g x) ∧
    (∀ sigma₁ sigma₂ : ℝ → ℂ, ContinuousOn sigma₁ (Icc (-M0) M0) →
      ContinuousOn sigma₂ (Icc (-M0) M0) →
      (∀ x ∈ Ioo (-M0) M0,
        -(1 / 2) * sigma₁ x + Complex.I * k * alpha * singleLayer k M0 sigma₁ x 0 = g x) →
      (∀ x ∈ Ioo (-M0) M0,
        -(1 / 2) * sigma₂ x + Complex.I * k * alpha * singleLayer k M0 sigma₂ x 0 = g x) →
      EqOn sigma₁ sigma₂ (Icc (-M0) M0)) := by sorry

end Arxiv1507_03491
