-- Prove2me | Theorems.Thm_Arxiv1707_02146_bbtm_intensity_decomposition
-- name    : Arxiv1707_02146.bbtm_intensity_decomposition
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T00:18:15.627502+00:00
-- url     : https://prove2.me/theorems/7e1ff3eb-32b9-484b-a504-1821977ecfff
-- title:
--   Eq. (1): the broadband intensity is linear in the SLM field through the Broadband Transmission Matrix
-- statement:
--   Let $N_\lambda$ spectral channels, $n$ modulated SLM pixels and $m$ camera pixels be given, with reference output fields $E^{out,R}(\lambda_i)\in\mathbb{C}^m$ and monochromatic transmission matrices $T(\lambda_i)\in\mathbb{C}^{m\times n}$. Write $E^{out,M}(\lambda_i)=T(\lambda_i)E^{in}(\lambda_i)$.
--
--   1. For all input fields $E^{in}(\lambda_i)\in\mathbb{C}^n$ and every camera pixel $x$,
--   $$I_x=\sum_{i}\big|E^{out,R}_x(\lambda_i)+E^{out,M}_x(\lambda_i)\big|^2=I_{0,x}+\sum_i\Big[\big(E^{out,R}_x(\lambda_i)\big)^*E^{out,M}_x(\lambda_i)+\text{c.c.}\Big],$$
--   where $I_{0,x}=\sum_i\big(|E^{out,R}_x(\lambda_i)|^2+|E^{out,M}_x(\lambda_i)|^2\big)$.
--   2. If the field on the modulated SLM pixels is the same for all spectral components, $E^{in}(\lambda_i)=e^{i\varphi}E$ with $E\in\mathbb{C}^n$ and a phase shift $\varphi\in\mathbb{R}$ common to all $\lambda_i$, then
--   $$I_x=I_{0,x}+2\,\mathrm{Re}\big(e^{i\varphi}(BE)_x\big),\qquad B=\sum_{i=1}^{N_\lambda}T'(\lambda_i),\quad T'(\lambda_i)=\big(E^{out,R}(\lambda_i)\big)^*T(\lambda_i),$$
--   and the static term $I_{0,x}$ does not depend on $\varphi$.
--
--   So the part of the broadband intensity that depends on the SLM phase is linear in the SLM field through the single operator $B$, the Broadband Transmission Matrix.
--
--   **Formalization Note** The third line of the paper's eq. (1) omits the "+ c.c." of the second line; the statement keeps it, which gives the factor $2\,\mathrm{Re}$. The paper's narrowband assumption $\Delta\lambda/\lambda_0\ll1$ is used only to make the phase shift, and the SLM field, the same for all spectral components; this is written as the hypothesis $E^{in}(\lambda_i)=e^{i\varphi}E$. The product $(E^{out,R}(\lambda_i))^*T(\lambda_i)$ is taken row by row: row $x$ of $T(\lambda_i)$ is multiplied by the conjugate reference field at pixel $x$.
-- source:
--   Mounaix, de Aguiar and Gigan, Temporal recompression through a scattering medium via a broadband transmission matrix, arXiv:1707.02146v1 (2017), claim c011; main text (unnumbered), eq. (1) and the paragraph defining B that follows it, PDF p. 2

import Mathlib
import Definitions.Def_Arxiv1707_02146_Basic

open Matrix ComplexConjugate

namespace Arxiv1707_02146

theorem bbtm_intensity_decomposition {N m n : ℕ} (ER : Fin N → Fin m → ℂ)
    (T : Fin N → Matrix (Fin m) (Fin n) ℂ) :
    (∀ (Ein : Fin N → Fin n → ℂ) (x : Fin m),
      (broadbandIntensity ER T Ein x : ℂ) = (staticTerm ER T Ein x : ℂ) +
        ∑ i, (conj (ER i x) * modulatedField T Ein i x +
          conj (conj (ER i x) * modulatedField T Ein i x))) ∧
    (∀ (E : Fin n → ℂ) (φ : ℝ) (x : Fin m),
      broadbandIntensity ER T (fun _ => Complex.exp (φ * Complex.I) • E) x =
          staticTerm ER T (fun _ => E) x +
            2 * (Complex.exp (φ * Complex.I) * (bbtm ER T *ᵥ E) x).re ∧
        staticTerm ER T (fun _ => Complex.exp (φ * Complex.I) • E) x =
          staticTerm ER T (fun _ => E) x) := by sorry

end Arxiv1707_02146
