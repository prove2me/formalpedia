-- Prove2me | Theorems.Thm_Arxiv2005_04287_speckleSNR_below_rayleigh
-- name    : Arxiv2005_04287.speckleSNR_below_rayleigh
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T09:13:04.135819+00:00
-- url     : https://prove2.me/theorems/0d013449-f792-5c94-9e6c-7ece5fdc65fc
-- title:
--   Discussion, p. 19: the Burr, Lomax and logistic models give a speckle SNR below the Rayleigh value $1.91$
-- statement:
--   Let $b>2$, $\lambda>0$ and $\lambda_2>0$. The speckle signal-to-noise ratio (mean over standard deviation of the echo amplitude) is below the Rayleigh value $\sqrt{\pi/(4-\pi)}\approx1.91$ under each of the three models:
--
--   1. the Burr model, where the amplitude $A$ has density (10);
--   2. the Lomax model, where the intensity $I$ has density (14) and the amplitude is $\sqrt I$;
--   3. the logistic model, where $y=\ln A$ has density (15) and the amplitude is $e^y$.
--
--   In each case the amplitude has a finite second moment.
--
--   **Formalization Note** The paper does not say which variable the SNR refers to, nor for which $b$. The statement uses the amplitude in all three models, because the benchmark $1.91$ (Burckhardt, ref. 9) is the Rayleigh SNR of the amplitude; the intensity and log amplitude are converted back to the amplitude. The SNR exists only when the amplitude has finite variance, which for these laws means $b>2$. The benchmark is the exact Rayleigh value $\sqrt{\pi/(4-\pi)}=1.9130\ldots$. Against the rounded $1.91$ the claim fails for large $b$: the Burr SNR at $b=1000$ is $1.9119$. After conversion to the amplitude, models 2 and 3 are again Burr laws, with scales $\sqrt{\lambda_2}$ and $\lambda$. The SNR of a Burr law does not depend on its scale, so the three bounds are one inequality. They are listed separately because the paper names three models.
-- source:
--   K. J. Parker and S. S. Poul, Burr, Lomax, Pareto, and Logistic Distributions from Ultrasound Speckle, arXiv:2005.04287v1 (2020), claim c013; Discussion and Conclusion, PDF p. 19 (ref. 9)

import Mathlib
import Definitions.Def_Arxiv2005_04287_Basic

open MeasureTheory ProbabilityTheory

namespace Arxiv2005_04287

theorem speckleSNR_below_rayleigh (b lam lam2 : ℝ) (hb : 2 < b) (hlam : 0 < lam) (hlam2 : 0 < lam2) :
    (Integrable (fun A : ℝ => A ^ 2) (burrMeasure b lam) ∧
      speckleSNR (burrMeasure b lam) < rayleighSNR) ∧
    (Integrable (fun A : ℝ => A ^ 2) ((intensityMeasure b lam2).map Real.sqrt) ∧
      speckleSNR ((intensityMeasure b lam2).map Real.sqrt) < rayleighSNR) ∧
    (Integrable (fun A : ℝ => A ^ 2) ((logAmpMeasure b lam).map Real.exp) ∧
      speckleSNR ((logAmpMeasure b lam).map Real.exp) < rayleighSNR) := by sorry

end Arxiv2005_04287
